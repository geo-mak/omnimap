use core::fmt::{Debug, Display};
use core::hash::{Hash, Hasher};
use core::hint::unreachable_unchecked;
use core::iter::Map;
use core::mem::ManuallyDrop;
use core::ops::{Index, IndexMut};
use core::slice::{Iter, IterMut};
use core::{fmt, mem};

use std::collections::hash_map::DefaultHasher;

use crate::alloc::MemorySpace;
use crate::error::{AllocError, OnError};
use crate::index::{MapIndex, Tag};
use crate::opt::OnDrop;
use crate::opt::branch_prediction::{likely, unlikely};

struct FindResult {
    slot: usize,
    entry: usize,
}

impl FindResult {
    #[inline(always)]
    const fn just_slot(slot: usize) -> Self {
        Self {
            slot,
            // Invalid offset used as a sentinel value to indicate absence.
            entry: usize::MAX,
        }
    }

    #[inline(always)]
    const fn entry_exists(&self) -> bool {
        self.entry != usize::MAX
    }
}

pub struct Entry<K, V> {
    key: K,
    value: V,
    hash: usize,
}

impl<K, V> Entry<K, V> {
    #[inline(always)]
    const fn new(key: K, value: V, hash: usize) -> Self {
        Self { key, value, hash }
    }
}

impl<K, V> Clone for Entry<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            value: self.value.clone(),
            hash: self.hash,
        }
    }
}

impl<K, V> Debug for Entry<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Entry")
            .field("key", &self.key)
            .field("value", &self.value)
            .field("hash", &self.hash)
            .finish()
    }
}

/// An immutable iterable view of the entries in the map.
pub type EntriesIterator<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> (&K, &V)>;

/// A mutable iterable view of the entries in the map.
///
/// The keys are immutable, only the values can be modified.
pub type EntriesIteratorMut<'a, K, V> =
    Map<IterMut<'a, Entry<K, V>>, fn(&mut Entry<K, V>) -> (&K, &mut V)>;

/// Stores the fields of the map and allocates/deallocates its pointers.
/// It does't implement `Drop`. Deallocation is manual.
struct MapData<K, V> {
    entries: MemorySpace<Entry<K, V>>,
    index: MapIndex,
    cap: usize,
    len: usize,
    deleted: usize,
}

impl<K, V> MapData<K, V> {
    #[inline(always)]
    const fn new() -> Self {
        Self {
            // Unallocated pointers.
            entries: MemorySpace::new(),
            index: MapIndex::new_unallocated(),
            cap: 0,
            len: 0,
            deleted: 0,
        }
    }

    /// Creates a new allocated instance according the to the specified capacity `cap`.
    ///
    /// If `INIT` is true, the index will initialize its control bytes, otherwise the control bytes
    /// will remain uninitialized.
    ///
    /// Error handling depends on the error handling context `on_err`.
    ///
    /// Note: the size of `new_cap` must be greater than `0` and within the range of `isize::MAX`
    /// bytes to be considered a valid size, but successful allocation remains not guaranteed.
    fn new_allocate<const INIT: bool>(
        cap: usize,
        on_err: OnError,
    ) -> Result<MapData<K, V>, AllocError> {
        unsafe {
            let mut entries: MemorySpace<Entry<K, V>> = MemorySpace::new();

            let layout = entries.make_layout(cap, on_err)?;

            let mut index = MapIndex::new_allocate_uninit(cap, on_err)?;

            let error_guard = OnDrop::set(cap, |cap| index.deallocate(*cap));

            entries.allocate(layout, on_err)?;

            error_guard.finish();

            if INIT {
                index.set_tags_empty(cap);
            }

            let instance = MapData {
                index,
                entries,
                cap,
                len: 0,
                deleted: 0,
            };

            Ok(instance)
        }
    }

    /// Calls drop on initialized elements in entries.
    ///
    /// # Safety
    ///
    /// Data must be allocated before calling this method.
    #[inline(always)]
    unsafe fn drop_initialized(&mut self) {
        unsafe { self.entries.drop_initialized(self.len) };
    }

    /// Deallocates index and entries **without** resetting the fields.
    /// It doesn't call drop on initialized items either.
    ///
    /// # Safety
    ///
    /// Data must be allocated before calling this method.
    #[inline]
    unsafe fn deallocate(&mut self) {
        unsafe {
            let layout = self.entries.make_layout_unchecked(self.cap);
            self.entries.deallocate(layout);
            self.index.deallocate(self.cap);
        }
    }

    /// Builds the index of the map according to the current entries and the capacity of the index.
    /// This method should be called **only** after resetting the index.
    const fn build_index(&mut self) {
        let mut i = 0;
        unsafe {
            while i < self.len {
                let entry = self.entries.access(i);
                let mut slot = entry.hash % self.cap;

                'probing: loop {
                    let tag = self.index.tag_ref_mut(slot);
                    if tag.is_empty() {
                        *tag = Tag::Occupied;
                        self.index.store_entry_index(slot, i);
                        break 'probing;
                    }

                    debug_assert!(
                        !tag.is_deleted(),
                        "Logic error: detected deleted slot while building index"
                    );

                    slot = (slot + 1) % self.cap;
                }

                i += 1;
            }
        }
    }
}

/// A key-value data structure with hash-based indexing and ordered storage of entries, providing
/// fast insertion, deletion, and retrieval of entries.
///
/// It offers intuitive and ergonomic APIs inspired by hash maps and vectors, with the added
/// benefit of predictable iteration order and stable indices.
pub struct OmniMap<K, V> {
    data: MapData<K, V>,
}

// Core implementation
impl<K, V> OmniMap<K, V>
where
    K: Eq + Hash,
{
    const DEFAULT_CAPACITY: usize = 16;

    /// Returns a new `OmniMap` without allocated capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::new();
    ///
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 0);
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        OmniMap {
            data: MapData::new(),
        }
    }

    /// Creates a new `OmniMap` with the specified `capacity`.
    ///
    /// # Panics
    ///
    /// This function will panic if capacity overflow occurs, or when allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::with_capacity(10);
    ///
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.capacity(), 10);
    /// ```
    #[must_use]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity == 0 {
            return Self::new();
        }

        unsafe {
            let cap = match Self::allocation_capacity(capacity, OnError::NoReturn) {
                Ok(cap) => cap,
                Err(_) => unreachable_unchecked(),
            };

            match MapData::new_allocate::<true>(cap, OnError::NoReturn) {
                Ok(data) => OmniMap { data },
                Err(_) => unreachable_unchecked(),
            }
        }
    }

    /// Returns the allocated _usable_ capacity of the `OmniMap`.
    ///
    /// The actual allocated capacity is higher to maintain the load factor.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::new();
    /// assert_eq!(map.capacity(), 0);
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::default();
    /// assert_eq!(map.capacity(), 16);
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::with_capacity(10);
    /// assert_eq!(map.capacity(), 10);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        (self.data.cap >> 3) * 7 + ((self.data.cap & 7) * 7 >> 3)
    }

    /// Returns the number of entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.data.len
    }

    /// Checks if the `OmniMap` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::new();
    ///
    /// assert!(map.is_empty());
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    ///
    /// assert!(!map.is_empty());
    /// ```
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.data.len == 0
    }

    /// Calculates the hash value for a key.
    ///
    /// > Note: The hash method of the `key` may panic.
    #[inline]
    fn make_hash(key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize
    }

    /// Returns the value that maintains the load factor for a given capacity `given`.
    ///
    /// This method doesn't check for arithmetic overflow.
    #[must_use]
    #[inline(always)]
    const fn allocation_capacity_unchecked(given: usize) -> usize {
        ((given + 1) * 8) / 7
    }

    /// Returns the value that maintains the load factor for a given capacity `given`.
    ///
    /// This method checks for arithmetic overflow.
    #[inline(always)]
    const fn allocation_capacity(given: usize, on_err: OnError) -> Result<usize, AllocError> {
        if let Some(plus_one) = given.checked_add(1) {
            if let Some(mul_eight) = plus_one.checked_mul(8) {
                // Can't overflow.
                return Ok(mul_eight / 7);
            }
        }
        Err(on_err.overflow())
    }

    /// Returns the next power of two of the current capacity.
    ///
    /// This method panics when overflow occurs.
    #[inline(always)]
    const fn capacity_next_power_of_two(&self) -> usize {
        match Self::allocation_capacity(self.data.cap, OnError::NoReturn) {
            Ok(alloc_cap) => alloc_cap.next_power_of_two(),
            Err(_) => unsafe { unreachable_unchecked() },
        }
    }

    /// Creates a new allocated instance according the to the specified capacity `cap`.
    ///
    /// If `INIT` is true, the index will initialize its control bytes, otherwise the control bytes
    /// will remain uninitialized.
    ///
    /// Error handling depends on the error handling context `on_err`.
    ///
    /// Note: the size of `new_cap` must be greater than `0` and within the range of `isize::MAX`
    /// bytes to be considered a valid size, but successful allocation remains not guaranteed.
    ///
    /// # Safety
    ///
    /// This method should be called **only** when the map is still unallocated.
    #[inline(always)]
    fn allocate<const INIT: bool>(
        &mut self,
        cap: usize,
        on_err: OnError,
    ) -> Result<(), AllocError> {
        debug_assert_eq!(self.data.cap, 0);
        // Deallocation guard is not required, because self.data is supposed to be unallocated.
        // When swap finishes, data will simply be discarded.
        let mut data = MapData::new_allocate::<INIT>(cap, on_err)?;
        // State transition.
        mem::swap(&mut self.data, &mut data);
        Ok(())
    }

    /// Shrinks or grows the allocated memory space to the specified `new_cap`.
    ///
    /// This method will also reset the index and rebuild it according to the new capacity.
    ///
    /// On error, the map's state will not be affected.
    ///
    /// # Safety
    ///
    /// This method should be called only when the map is already allocated.
    fn reallocate_reindex(&mut self, new_cap: usize, on_err: OnError) -> Result<(), AllocError> {
        unsafe {
            let new_data = MapData::<K, V>::new_allocate::<true>(new_cap, on_err)?;

            let mut protected_data = OnDrop::set(new_data, |data| {
                data.deallocate();
            });

            core::ptr::copy_nonoverlapping(
                self.data.entries.ptr(), // <- Non-null check inside.
                protected_data.arg.entries.ptr_mut(),
                self.data.len,
            );

            protected_data.arg.len = self.data.len;
            protected_data.arg.build_index();

            // protected_data points now to previous `self` data.
            // It will be deallocated when dropped without calling drop on entries.
            mem::swap(&mut self.data, &mut protected_data.arg);
            Ok(())
        }
    }

    /// Deallocates the entries and the index without calling `drop` on the initialized entries.
    ///
    /// Fields of capacity, length, and deleted counter will be reset to `0`.
    ///
    /// # Safety
    ///
    /// Index and entries must be allocated before calling this method.
    fn deallocate(&mut self) {
        unsafe {
            self.data.deallocate();
        }

        // Reset fields.
        self.data.cap = 0;
        self.data.len = 0;
        self.data.deleted = 0;
    }

    /// Decrements the index of all occupied slots with index value greater than `after` by using
    /// linear search.
    ///
    /// The search domain is `[0, capacity - 1]`.
    const fn decrement_index_linear(&mut self, after: usize) {
        let mut i = 0;
        unsafe {
            while i < self.data.cap {
                if self.data.index.read_tag(i).is_occupied() {
                    let index = self.data.index.entry_index_ref_mut(i);
                    if *index > after {
                        *index -= 1;
                    }
                }
                i += 1
            }
        }
    }

    /// Decrements the index of occupied slots by using the hash value of each entry after `after`
    /// to find its slot.
    ///
    /// The search domain starts from `after` as exclusive bound and ends with `inc_end` as
    /// inclusive upper bound.
    const fn decrement_index_hash(&mut self, after: usize, inc_end: usize) {
        let mut i = after + 1;
        unsafe {
            while i <= inc_end {
                let hash = self.data.entries.access(i).hash;
                let mut slot = hash % self.data.cap;

                'probing: loop {
                    if self.data.index.read_tag(slot).is_occupied() {
                        let index = self.data.index.entry_index_ref_mut(slot);
                        if *index == i {
                            *index -= 1;
                            break 'probing;
                        }
                    }

                    slot = (slot + 1) % self.data.cap
                }

                i += 1;
            }
        }
    }

    /// Decrements the index of the occupied slots.
    ///
    /// Parameters:
    ///  - `after`: the position to decrement after it.
    ///  - `inc_end`: an **inclusive** upper bound for decrementing.
    ///
    /// Decrementing applies one of two methods to find the target slots.
    ///
    /// - If `inc_end - after` is greater than `capacity/2`, the search for the affected slots will
    ///   be linear decrementing all encountered occupied slots in the index with value greater than
    ///   `after` within the range `[0, capacity - 1]`.
    ///
    /// - If `inc_end - after` is less than or equal to `capacity/2`, the search for the target
    ///   slots will be very specific using the hash value of the entries starting from offset
    ///   `from + 1` to `inc_end` as an inclusive upper bound.
    #[inline]
    const fn decrement_index(&mut self, after: usize, inc_end: usize) {
        let count = inc_end - after;
        if count > self.data.cap / 2 {
            self.decrement_index_linear(after);
        } else {
            // It has probing overhead, but it can skip large sequences.
            self.decrement_index_hash(after, inc_end);
        }
    }

    /// Resets and rebuilds the index of the map according to the current entries and the capacity
    /// of the index.
    #[inline(always)]
    fn reindex(&mut self) {
        unsafe { self.data.index.set_tags_empty(self.data.cap) };
        self.data.deleted = 0;
        self.data.build_index();
    }

    /// Reclaims deleted slots if suitable or reserves more capacity according to the load factor.
    ///
    /// This method panics when overflow occurs or when allocation fails.
    fn reclaim_or_reserve(&mut self) {
        if self.data.len < self.data.cap >> 1 {
            // Reclaiming deleted slots without reallocation.
            self.reindex();
        } else {
            // Reallocation.
            if likely(self.data.cap != 0) {
                let new_cap = self.capacity_next_power_of_two();
                match self.reallocate_reindex(new_cap, OnError::NoReturn) {
                    Ok(_) => (),
                    Err(_) => unsafe { unreachable_unchecked() },
                }
            } else {
                match self.allocate::<true>(4, OnError::NoReturn) {
                    Ok(_) => (),
                    Err(_) => unsafe { unreachable_unchecked() },
                }
            }
        }
    }

    /// Tries to reserve `additional` capacity.
    ///
    /// All internal calls are checked, with result depends on the error handling context `on_err`.
    fn reserve_additional(&mut self, additional: usize, on_err: OnError) -> Result<(), AllocError> {
        if likely(additional != 0) {
            let extra_cap = Self::allocation_capacity(additional, on_err)?;
            if likely(self.data.cap != 0) {
                match self.data.cap.checked_add(extra_cap) {
                    Some(new_cap) => self.reallocate_reindex(new_cap, on_err),
                    None => Err(on_err.overflow()),
                }
            } else {
                match self.allocate::<true>(extra_cap, on_err) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(e),
                }
            }
        } else {
            Ok(())
        }
    }

    /// Reserves capacity for `additional` elements in advance.
    ///
    /// The resulting capacity will be equal to `self.core.capacity() + additional` or _more_ to
    /// maintain the load factor.
    ///
    /// This method is no-op if `additional` is `0`.
    ///
    /// # Panics
    ///
    /// This method will panic if capacity overflow occurs, or when allocation fails.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// // The allocated capacity with first insert is 4.
    /// map.insert(1, "a");
    ///
    /// // Reserve space for 10 more elements
    /// map.reserve(10);
    ///
    /// // The capacity is now 14
    /// assert_eq!(map.capacity(), 14);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        match self.reserve_additional(additional, OnError::NoReturn) {
            Ok(_) => (),
            // Hints the compiler that the error branch can be eliminated from the call chain.
            Err(_) => unsafe { unreachable_unchecked() },
        };
    }

    /// Tries to reserve capacity for `additional` elements in advance.
    ///
    /// This method is semantically equivalent to [`OmniMap::reserve`], except that it returns an
    /// error instead of panicking when the allocation fails.
    ///
    /// The resulting capacity will be equal to `self.core.capacity() + additional` or _more_ to
    /// maintain the load factor.
    ///
    /// This method is no-op if `additional` is `0`.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::{AllocError, OmniMap};
    ///
    /// let mut map = OmniMap::new();
    ///
    /// // The allocated capacity with first insert is 4.
    /// map.insert(1, "a");
    ///
    /// // Try reserve space for very large number of elements.
    /// let mut result = map.try_reserve(usize::MAX);
    ///
    /// // Result must be error.
    /// assert!(matches!(result.err().unwrap(), AllocError::Overflow));
    ///
    /// // The capacity remains 3
    /// assert_eq!(map.capacity(), 3);
    ///
    /// // Reserve space for 10 more elements
    /// result = map.try_reserve(10);
    ///
    /// assert!(result.is_ok());
    ///
    /// // The capacity is now 14
    /// assert_eq!(map.capacity(), 14);
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), AllocError> {
        self.reserve_additional(additional, OnError::ReturnErr)
    }

    /// Finds the slot of the key in the index.
    ///
    /// If the key already exists, the returned `slot` is the index of its slot and `entry`
    /// is the index of its entry.
    ///
    /// If the key doesn't exist, the returned `slot` is free for inserting and the value
    /// of `entry` is an **invalid** index.
    ///
    /// # Safety
    ///
    /// Before using `entry`, its value must be checked first with `entry_exists()` method,
    /// because its value can be an invalid index.
    fn find(&self, hash: usize, key: &K) -> FindResult {
        unsafe {
            let mut slot = hash % self.data.cap;
            loop {
                match self.data.index.read_tag(slot) {
                    Tag::Occupied => {
                        let entry = self.data.index.read_entry_index(slot);
                        if self.data.entries.access(entry).key == *key {
                            return FindResult { slot, entry };
                        }
                    }
                    Tag::Empty => return FindResult::just_slot(slot),
                    Tag::Deleted => {}
                }
                slot = (slot + 1) % self.data.cap;
            }
        }
    }

    /// Inserts a key-value pair into the map.
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Parameters
    ///
    /// - `key`: The key to insert or update.
    ///
    /// - `value`: The value to associate with the key.
    ///
    /// # Panics
    ///
    /// This method will panic if capacity overflow occurs, or when allocation fails.
    ///
    /// # Time Complexity
    ///
    /// _O_(1) Amortized.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    ///  // When inserting a new key-value pair, None is returned
    ///  map.insert(1, "a");
    ///  map.insert(2, "b");
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"b"));
    ///
    /// // Update the value for an existing key
    /// let old_value = map.insert(1, "c");
    ///
    /// // The old value is returned
    /// assert_eq!(old_value, Some("a"));
    ///
    /// // The value is updated
    /// assert_eq!(map.get(&1), Some(&"c"));
    /// ```
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if unlikely(self.data.len + self.data.deleted == self.capacity()) {
            self.reclaim_or_reserve();
        }

        let hash = Self::make_hash(&key);

        let result = self.find(hash, &key);

        if result.entry_exists() {
            let entry = unsafe { self.data.entries.access_mut(result.entry) };
            let old_val = mem::replace(&mut entry.value, value);
            return Some(old_val);
        };

        unsafe {
            debug_assert!(
                self.data.index.read_tag(result.slot).is_empty(),
                "Logic error: attempt to overwrite a non-empty slot while inserting"
            );

            self.data
                .entries
                .store(self.data.len, Entry::new(key, value, hash));
            self.data
                .index
                .store(result.slot, Tag::Occupied, self.data.len);
        }

        self.data.len += 1;

        // Key was new and inserted.
        None
    }

    /// Retrieves a value by its `key`.
    ///
    /// # Returns
    ///
    /// - `Some(&value)`: if the key is found.
    ///
    /// - `None`: if the key does not exist.
    ///
    /// # Time Complexity
    ///
    /// _O_(1) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    ///  map.insert(1, "a");
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    ///
    /// // Key does not exist
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[must_use]
    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        if self.is_empty() {
            return None;
        }

        let hash = Self::make_hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &self.data.entries.access(result.entry).value };
            return Some(value);
        }

        None
    }

    /// Retrieves a mutable reference to a value by its `key`.
    ///
    /// # Returns
    ///
    /// - `Some(&mut value)`: If the key is found.
    ///
    /// - `None`: If the key does not exist.
    ///
    /// # Time Complexity
    ///
    /// _O_(1) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    ///
    /// if let Some(value) = map.get_mut(&1) {
    ///     *value = "b";
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&"b"));
    ///
    /// // Key does not exist
    /// assert_eq!(map.get_mut(&2), None);
    /// ```
    #[must_use]
    #[inline]
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if self.is_empty() {
            return None;
        }

        let hash = Self::make_hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &mut self.data.entries.access_mut(result.entry).value };
            return Some(value);
        }

        None
    }

    /// Returns the first entry in the map.
    ///
    /// # Returns
    ///
    /// - `Some((&key, &value))`: If the map is not empty.
    ///
    /// - `None`: If the map is empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.first(), Some((&1, &"a")));
    /// ```
    #[must_use]
    #[inline]
    pub const fn first(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        let entry = unsafe { self.data.entries.access_first() };

        Some((&entry.key, &entry.value))
    }

    /// Returns the last entry in the map.
    ///
    /// # Returns
    ///
    /// - `Some((&key, &value))`: If the map is not empty.
    ///
    /// - `None`: If the map is empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.last(), Some((&3, &"c")));
    /// ```
    #[must_use]
    #[inline]
    pub const fn last(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None;
        }

        let entry = unsafe { self.data.entries.access(self.data.len - 1) };

        Some((&entry.key, &entry.value))
    }

    /// Returns `true` if the map contains a value for the specified `key`.
    ///
    /// # Time Complexity
    ///
    /// _O_(1) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    ///
    /// // Key exists.
    /// assert!(map.contains_key(&1));
    ///
    /// // Key does not exist.
    /// assert!(!map.contains_key(&2));
    /// ```
    #[must_use]
    #[inline]
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Removes an entry by its `key` and returns its value.
    ///
    /// If `SHIFT` is `true`, this method will shift all entries after it to fill the gab, and
    /// updates their slots.
    ///
    /// If `SHIFT` is `false`, this method will copy the last entry to the place of the removed
    /// entry without shifting, and updates its slot.
    ///
    /// # Safety
    ///
    /// Map must not be empty when calling this method.
    #[inline]
    fn remove_entry<const SHIFT: bool>(&mut self, key: &K) -> Option<V> {
        let hash = Self::make_hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let index = result.entry;

            self.data.len -= 1;
            self.data.deleted += 1;

            unsafe {
                self.data.index.store_tag(result.slot, Tag::Deleted);
                let removed = self.data.entries.read_for_ownership(index).value;

                if likely(index != self.data.len) {
                    if SHIFT {
                        // Call order matters.
                        self.decrement_index(index, self.data.len);
                        self.data.entries.shift_left(index, self.data.len - index);
                    } else {
                        let last = self.data.entries.access(self.data.len);
                        let swapped = self.find(last.hash, &last.key);
                        self.data.index.store_entry_index(swapped.slot, index);
                        self.data.entries.memmove_one(self.data.len, index);
                    }
                }

                return Some(removed);
            };
        }

        // Key was not found.
        None
    }

    /// Removes an entry by its `key`.
    ///
    /// If the removed entry is not the last one, this method shifts all elements after it to fill
    /// the gab, which can be a significant performance overhead, especially with large number of
    /// entries.
    ///
    /// If a strict order preservation is not required, consider using [`OmniMap::swap_remove`]
    /// instead, which swaps the place of the last entry with the place of the removed entry to
    /// fill the gab, without shifting.
    ///
    /// # Returns
    ///
    /// - `Some(value)`: If key's entry is found and removed.
    ///
    /// - `None`: If the key does not have entry.
    ///
    /// # Time Complexity
    ///
    /// - _O_(n) on average.
    ///
    /// - _O_(1) on average, if the key is of the last entry.
    ///
    /// # Note
    /// This method does not shrink the current capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.len(), 2);
    ///
    /// // Remove an existing key
    /// assert_eq!(map.shift_remove(&1), Some("a"));
    ///
    /// assert_eq!(map.len(), 1);
    ///
    /// // Remove a non-existing key
    /// assert_eq!(map.shift_remove(&1), None);
    /// ```
    pub fn shift_remove(&mut self, key: &K) -> Option<V> {
        if self.is_empty() {
            return None;
        }
        self.remove_entry::<true>(key)
    }

    /// Removes an entry by its `key`, and swaps its place with the last entry.
    ///
    /// This method can be significantly faster than [`OmniMap::shift_remove`], if a strict order
    /// preservation is not required.
    ///
    /// # Returns
    ///
    /// - `Some(value)`: If key's entry is found and removed.
    ///
    /// - `None`: If the key does not have entry.
    ///
    /// # Time Complexity
    ///
    /// - _O_(1) on average.
    ///
    /// # Note
    /// This method does not shrink the current capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// // Remove an existing key by swapping.
    /// assert_eq!(map.swap_remove(&1), Some("a"));
    ///
    /// assert_eq!(map.len(), 2);
    ///
    /// // The last entry has been swapped, and it is accessible at the index of the removed entry.
    /// assert_eq!(map[0], "c");
    /// ```
    pub fn swap_remove(&mut self, key: &K) -> Option<V> {
        if self.is_empty() {
            return None;
        }
        self.remove_entry::<false>(key)
    }

    /// Pops the first entry from the map.
    /// The capacity of the map remains unchanged.
    ///
    /// # Returns
    ///
    /// - `Some((key, value))`: If the map is not empty.
    ///
    /// - `None`: If the map is empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.pop_front(), Some((1, "a")));
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn pop_front(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None;
        }

        // SAFETY: The map is not empty, so an entry must exist.
        let entry_ref = unsafe { self.data.entries.access_first() };

        let result = self.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.data.len -= 1;
        self.data.deleted += 1;

        unsafe {
            self.data.index.store_tag(result.slot, Tag::Deleted);
            let removed = self.data.entries.read_for_ownership(0);

            // Call order matters.
            self.decrement_index(0, self.data.len);
            self.data.entries.shift_left(0, self.data.len);

            Some((removed.key, removed.value))
        }
    }

    /// Pops the last entry from the map.
    /// The capacity of the map remains unchanged.
    ///
    /// # Returns
    ///
    /// - `Some((key, value))`: If the map is not empty.
    ///
    /// - `None`: If the map is empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(1) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.pop(), Some((3, "c")));
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn pop(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None;
        }

        let entry_ref = unsafe { self.data.entries.access(self.data.len - 1) };

        let result = self.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.data.len -= 1;
        self.data.deleted += 1;

        unsafe {
            self.data.index.store_tag(result.slot, Tag::Deleted);
            let removed = self.data.entries.read_for_ownership(self.data.len);

            Some((removed.key, removed.value))
        }
    }

    /// Shrinks or deallocates the map depending on its length.
    /// Extra reserves will be added to `base_cap` according to the current load factor.
    #[inline]
    fn shrink_or_deallocate(&mut self, base_cap: usize) {
        if likely(self.data.len > 0) {
            let new_cap = Self::allocation_capacity_unchecked(base_cap);
            match self.reallocate_reindex(new_cap, OnError::NoReturn) {
                Ok(_) => (),
                Err(_) => unsafe { unreachable_unchecked() },
            }
        } else {
            self.deallocate();
        }
    }

    /// Shrinks the capacity of the `OmniMap` to the specified capacity.
    /// In order to take effect, `capacity` must be less than the current capacity
    /// and greater than or equal to the number of elements in the map.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::with_capacity(10);
    ///
    /// assert_eq!(map.capacity(), 10);
    ///
    /// // Insert some elements
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// // Shrink the capacity to 3
    /// map.shrink_to(5);
    ///
    /// assert_eq!(map.capacity(), 5);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, capacity: usize) {
        if likely(capacity >= self.data.len && capacity < self.capacity()) {
            self.shrink_or_deallocate(capacity);
        }
    }

    /// Shrinks the capacity of the `OmniMap` to fit its current length.
    /// If the capacity is equal to the number of elements in the map, this method will do nothing.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::with_capacity(10);
    ///
    /// assert_eq!(map.capacity(), 10 );
    ///
    /// // Insert some elements
    ///  map.insert(1, "a");
    ///  map.insert(2, "b");
    ///
    /// // Shrink the capacity to fit the current length
    /// map.shrink_to_fit();
    ///
    /// assert_eq!(map.capacity(), 2);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        if likely(self.capacity() > self.data.len) {
            self.shrink_or_deallocate(self.data.len);
        }
    }

    /// Clears the map, removing all entries.
    /// The capacity of the map remains unchanged.
    ///
    /// # Time Complexity
    ///
    /// _O_(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.len(), 2);
    ///
    /// map.clear();
    ///
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        if self.is_empty() {
            return;
        }

        // On panic, this will leak memory to avoid double-free when the destructor of the map runs,
        // which in its turn will cause another panic.
        let protected_clear = OnDrop::set(self, |current| {
            unsafe { current.data.index.set_tags_empty(current.data.cap) };
            current.data.len = 0;
            current.data.deleted = 0;
        });

        unsafe {
            protected_clear.arg.data.drop_initialized();
        }
    }

    /// Returns an iterator over the current entries.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    fn iter_entries(&self) -> Iter<'_, Entry<K, V>> {
        if self.data.len == 0 {
            return [].iter();
        };
        unsafe { self.data.entries.as_slice(self.data.len).iter() }
    }

    /// Returns a mutable iterator over the entries in the `OmniMap`.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    fn iter_entries_mut(&mut self) -> IterMut<'_, Entry<K, V>> {
        if self.data.len == 0 {
            return [].iter_mut();
        };
        unsafe { self.data.entries.as_slice_mut(self.data.len).iter_mut() }
    }

    /// Returns an iterator over the entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.iter().collect::<Vec<(&i32, &&str)>>(), vec![(&1, &"a"), (&2, &"b")]);
    /// ```
    #[inline]
    pub fn iter(&self) -> EntriesIterator<'_, K, V> {
        self.iter_entries().map(|entry| (&entry.key, &entry.value))
    }

    /// Returns a mutable iterator over the entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// for (key, value) in map.iter_mut() {
    ///     *value = "c";
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&"c"));
    /// assert_eq!(map.get(&2), Some(&"c"));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> EntriesIteratorMut<'_, K, V> {
        self.iter_entries_mut()
            .map(|entry| (&entry.key, &mut entry.value))
    }

    /// Returns an iterator over the keys in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.iter_keys().collect::<Vec<&i32>>(), vec![&1, &2]);
    /// ```
    #[inline]
    pub fn iter_keys(&self) -> impl Iterator<Item = &K> {
        self.iter_entries().map(|entry| &entry.key)
    }

    /// Returns an iterator over the values in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.iter_values().collect::<Vec<&&str>>(), vec![&"a", &"b"]);
    /// ```
    #[inline]
    pub fn iter_values(&self) -> impl Iterator<Item = &V> {
        self.iter_entries().map(|entry| &entry.value)
    }

    /// Returns the current load factor.
    ///
    /// If capacity is `0`, `0.0` will be returned, which implies that `0.0` as a result is not an
    /// indicator for available capacity. Use `capacity()` method for that particular case.
    #[inline(always)]
    pub const fn load_factor(&self) -> f64 {
        if self.data.cap == 0 {
            0.0
        } else {
            (self.data.len + self.data.deleted) as f64 / self.data.cap as f64
        }
    }
}

impl<K, V> Drop for OmniMap<K, V> {
    fn drop(&mut self) {
        if self.data.cap == 0 {
            return;
        }
        // (Cap > 0) -> entries and index are allocated.
        unsafe {
            // This call is safe even if the length is zero.
            self.data.drop_initialized();
            self.data.deallocate();
        }
    }
}

impl<K, V> Default for OmniMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new `OmniMap` with the default capacity.
    /// The default capacity is set to `16`.
    ///
    /// # Panics
    ///
    /// This function will panic when allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::default();
    ///
    /// assert_eq!(map.capacity(), 16);
    /// ```
    #[inline]
    fn default() -> Self {
        Self::with_capacity(Self::DEFAULT_CAPACITY)
    }
}

impl<K, V> Index<usize> for OmniMap<K, V> {
    type Output = V;

    /// Returns immutable reference to the value at the specified `index`.
    ///
    /// # Panics
    ///
    /// If the given index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map[0], "a");
    /// assert_eq!(map[1], "b");
    /// ```
    fn index(&self, index: usize) -> &V {
        assert!(index < self.data.len, "Index out of bounds.");
        unsafe { &self.data.entries.access(index).value }
    }
}

impl<K, V> IndexMut<usize> for OmniMap<K, V> {
    /// Returns mutable reference to the value at the specified `index`.
    ///
    /// # Panics
    ///
    /// If the given index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// map[0] = "c";
    /// map[1] = "d";
    ///
    /// assert_eq!(map[0], "c");
    /// assert_eq!(map[1], "d");
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut V {
        assert!(index < self.data.len, "Index out of bounds.");
        unsafe { &mut self.data.entries.access_mut(index).value }
    }
}

impl<'a, K, V> IntoIterator for &'a OmniMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a V);
    type IntoIter = EntriesIterator<'a, K, V>;

    /// Returns an iterator over the entries.
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut OmniMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = EntriesIteratorMut<'a, K, V>;

    /// Returns a mutable iterator over the entries.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V> PartialEq for OmniMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.data.len != other.len() {
            return false;
        }
        self.iter()
            .all(|(key, value)| other.get(key).is_some_and(|v| *value == *v))
    }
}

impl<K, V> OmniMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Makes new clone from the current instance with two modes: compact and normal.
    ///
    /// The map must be allocated and not empty before calling this method.
    fn make_clone<const COMPACT: bool>(&self) -> OmniMap<K, V> {
        let cap = if COMPACT {
            // len + required reserves.
            Self::allocation_capacity_unchecked(self.data.len)
        } else {
            self.data.cap
        };

        match MapData::new_allocate::<COMPACT>(cap, OnError::NoReturn) {
            Ok(data) => {
                let mut instance = OmniMap { data };
                debug_assert!(instance.data.cap == cap);
                unsafe {
                    // Unwind-safe. On panic, cloned items will be dropped.
                    instance
                        .data
                        .entries
                        .clone_from(self.data.entries.ptr(), self.data.len);
                    instance.data.len = self.data.len;
                    if COMPACT {
                        instance.data.deleted = 0;
                        instance.data.build_index();
                    } else {
                        instance.data.deleted = self.data.deleted;

                        instance
                            .data
                            .index
                            .copy_from(&self.data.index, self.data.cap);
                    }
                }
                instance
            }
            // Must diverge, nothing to handle.
            Err(_) => unsafe { unreachable_unchecked() },
        }
    }

    /// Returns a compact clone of the current instance.
    ///
    /// This method creates a clone of the `OmniMap` where the capacity of the internal
    /// storage is reduced to fit the current number of elements. This can help reduce
    /// memory usage if the map has a lot of unused capacity.
    ///
    /// # Panics
    ///
    /// This method will panic when allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::with_capacity(5);
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// let compact_clone = map.clone_compact();
    ///
    /// assert_eq!(compact_clone.len(), map.len());
    /// assert_eq!(compact_clone.capacity(), map.len());
    ///
    /// assert_eq!(compact_clone.get(&1), Some(&"a"));
    /// assert_eq!(compact_clone.get(&2), Some(&"b"));
    /// ```
    #[inline]
    pub fn clone_compact(&self) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        self.make_clone::<true>()
    }
}

impl<K, V> Clone for OmniMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Creates an identical clone of the current instance without changing the capacity.
    /// The new map will have the same capacity as the original regardless of the number of
    /// elements.
    ///
    /// If capacity is a concern, use the `clone_compact` method to create a clone with a capacity
    /// equal to the number of elements.
    ///
    /// # Panics
    ///
    /// This method will panic when allocation fails.
    #[inline]
    fn clone(&self) -> Self {
        // Return an unallocated instance if the original is unallocated.
        if self.data.cap == 0 {
            return Self::new();
        }
        self.make_clone::<false>()
    }
}

/// An owning iterator over the entries of the map.
pub struct OmniMapIterator<K, V> {
    entries: MemorySpace<Entry<K, V>>,
    cap: usize,
    offset: usize,
    end: usize,
}

impl<K, V> Iterator for OmniMapIterator<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // (offset < end) -> (end > 0) -> (cap > 0) -> pointer != null.
        if self.offset < self.end {
            let entry = unsafe {
                // Note: The destructor of the iterator must not call drop on this value,
                // or it will be double-drop.
                self.entries.read_for_ownership(self.offset)
            };
            self.offset += 1;
            Some((entry.key, entry.value))
        } else {
            None
        }
    }

    /// Returns the number of remaining entries in the iterator.
    ///
    /// This method calls [`len`] internally which you can use directly.
    ///
    /// [`len`]: OmniMapIterator::len()
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<K, V> ExactSizeIterator for OmniMapIterator<K, V> {
    /// Returns the number of remaining entries in the iterator.
    #[inline(always)]
    fn len(&self) -> usize {
        self.end - self.offset
    }
}

impl<K, V> Drop for OmniMapIterator<K, V> {
    fn drop(&mut self) {
        if self.entries.is_null() {
            return;
        }

        unsafe {
            // (offset < end) -> (end > 0) && the iterator is not exhausted.
            if self.offset < self.end {
                // Drop the remaining entries.
                self.entries.drop_range(self.offset..self.end);
            }

            // Infallible, uncontrolled. Already allocated.
            let layout = self.entries.make_layout_unchecked(self.cap);
            self.entries.deallocate(layout);
        }
    }
}

impl<K, V> IntoIterator for OmniMap<K, V> {
    type Item = (K, V);
    type IntoIter = OmniMapIterator<K, V>;

    /// Consumes the `OmniMap` and returns an iterator over its entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// let mut iter = map.into_iter();
    ///
    /// assert_eq!(iter.next(), Some((1, "a")));
    /// assert_eq!(iter.next(), Some((2, "b")));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        let mut iterator = OmniMapIterator {
            entries: MemorySpace::new(),
            cap: 0,
            end: 0,
            offset: 0,
        };

        if self.data.len == 0 {
            return iterator;
        }

        iterator.cap = self.data.cap;
        iterator.end = self.data.len;

        let mut manual_self = ManuallyDrop::new(self);

        // The fields that need deallocation are index and entries.
        // index must be deallocated here and entries shall be deallocated by the iterator.
        unsafe {
            manual_self.data.index.deallocate(iterator.cap);
            iterator.entries = manual_self.data.entries.duplicate();
        }

        iterator
    }
}

impl<K, V> Debug for OmniMap<K, V>
where
    K: Eq + Hash + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> Display for OmniMap<K, V>
where
    K: Display + Eq + Hash,
    V: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        // This call is safe even if the map is not allocated.
        for entry in self.iter_entries() {
            writeln!(f, "    {}: {}", entry.key, entry.value)?;
        }
        write!(f, "}}")
    }
}

/// Development and testing methods that are not available in release builds.
#[cfg(test)]
impl<K, V> OmniMap<K, V> {
    /// Returns the tag's value of the slot at the specified `offset`.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_tag(&self, offset: usize) -> Tag {
        debug_assert!(offset < self.data.cap);
        unsafe { self.data.index.read_tag(offset) }
    }

    /// Returns the slot's value at the specified `offset`.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_slot_value(&self, offset: usize) -> usize {
        debug_assert!(offset < self.data.cap);
        unsafe { self.data.index.read_entry_index(offset) }
    }

    /// Returns the number of deleted slots.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_deleted(&self) -> usize {
        self.data.deleted
    }

    /// Returns the number of allocated slots/entries.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_allocated_cap(&self) -> usize {
        self.data.cap
    }
}
