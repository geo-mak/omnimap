use core::fmt::{Debug, Display};
use core::hash::{Hash, Hasher};
use core::hint::unreachable_unchecked;
use core::iter::Map;
use core::mem::ManuallyDrop;
use core::ops::{Index, IndexMut};
use core::slice::{Iter, IterMut};
use core::{fmt, mem};

use std::collections::hash_map::DefaultHasher;

use crate::alloc::UnsafeBufferPointer;
use crate::error::{AllocError, OnError};
use crate::index::{MapIndex, Tag};
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
            // Outside the representable range of any allocation size or offset.
            entry: usize::MAX,
        }
    }

    #[inline(always)]
    const fn entry_exists(&self) -> bool {
        self.entry != usize::MAX
    }
}

#[derive(Debug)]
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

/// An immutable iterable view of the entries in the map.
pub type IterEntries<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> (&K, &V)>;

/// A mutable iterable view of the entries in the map.
///
/// The keys are immutable, only the values can be modified.
pub type IterEntriesMut<'a, K, V> =
    Map<IterMut<'a, Entry<K, V>>, fn(&mut Entry<K, V>) -> (&K, &mut V)>;

/// A key-value data structure with hash-based indexing and ordered storage of entries, providing
/// fast insertion, deletion, and retrieval of entries.
///
/// It offers intuitive and ergonomic APIs inspired by hash maps and vectors, with the added
/// benefit of predictable iteration order and stable indices.
pub struct OmniMap<K, V> {
    entries: UnsafeBufferPointer<Entry<K, V>>,
    index: MapIndex,
    cap: usize,
    len: usize,
    deleted: usize,
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
    /// use omni_map::OmniMap;
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
            // Unallocated pointers.
            entries: UnsafeBufferPointer::new(),
            index: MapIndex::new_unallocated(),
            cap: 0,
            len: 0,
            deleted: 0,
        }
    }

    /// Creates a new `OmniMap` with the specified `capacity`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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

            let mut instance = Self::new();

            match instance.allocate::<true>(cap, OnError::NoReturn) {
                Ok(_) => instance,
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
    /// use omni_map::OmniMap;
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
        (self.cap * 7) / 8
    }

    /// Returns the number of entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
        self.len
    }

    /// Checks if the `OmniMap` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
        self.len == 0
    }

    /// Calculates the hash value for a key.
    #[inline]
    fn make_hash(&self, key: &K) -> usize {
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
        match Self::allocation_capacity(self.cap, OnError::NoReturn) {
            Ok(alloc_cap) => alloc_cap.next_power_of_two(),
            Err(_) => unsafe { unreachable_unchecked() },
        }
    }

    /// Allocates the specified `cap`.
    ///
    /// On error, the map's state will not be affected, therefore this method shall be the only
    /// one used to allocate new instances, because it guards against partial allocations and
    /// invalid states when allocation fails.
    ///
    /// if `INIT` is:
    /// - `true`: this method will initialize the control tags of the index after allocation.
    /// - `false`: the control tags of the allocated index will remain uninitialized.
    ///
    /// On total success, fields entries, index and `cap` are set according the new state.
    ///
    /// Note: the size of `new_cap` must be greater than `0` and within the range of `isize::MAX`
    /// bytes to be considered a valid size, but successful allocation remains not guaranteed.
    ///
    /// # Safety
    ///
    /// This method should be called **only** when the map is not allocated.
    fn allocate<const INIT: bool>(
        &mut self,
        cap: usize,
        on_err: OnError,
    ) -> Result<(), AllocError> {
        // Important notes:
        // - This method is designed to be recoverable, the map's state must remain unchanged
        //   until a total success. All or none.
        //
        // - Allocation remains a runtime decision, it can fail regardless of the checking.
        unsafe {
            // The largest layout. Fallible, controlled.
            let layout = self.entries.make_layout(cap, on_err)?;

            // Index is much cheaper to deallocate on error.
            let mut index = MapIndex::new_unallocated();

            // Fallible, controlled.
            index.allocate_uninit(cap, on_err)?;

            // Activate index's guard to deallocate new index on sudden drop.
            let index_guard = index.guard(cap);

            // If the allocation fails, the allocated index will be deallocated by the guard.
            self.entries.allocate(layout, on_err)?;

            // Deactivate the guard.
            index_guard.deactivate();

            // Update fields.
            self.index = index;
            self.cap = cap;

            // Map's destructor is fully qualified.

            if INIT {
                // Initialize control tags.
                self.index.set_tags_empty(cap);
            }

            // Should be:
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
            // Infallible, uncontrolled. Already allocated.
            let layout = self.entries.make_layout_unchecked(self.cap);
            self.entries.deallocate(layout);
            self.index.deallocate(self.cap);
        }

        // Reset fields.
        self.cap = 0;
        self.len = 0;
        self.deleted = 0;
    }

    /// Builds the index of the map according to the current entries and the capacity of the index.
    /// This method should be called **only** after resetting the index.
    const fn build_index(&mut self) {
        let mut i = 0;
        unsafe {
            while i < self.len {
                let entry = self.entries.load(i);
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

    /// Decrements the index of all occupied slots with index value greater than `after` by using
    /// linear search.
    ///
    /// The search domain is `[0, capacity - 1]`.
    const fn decrement_index_linear(&mut self, after: usize) {
        let mut i = 0;
        unsafe {
            while i < self.cap {
                if self.index.read_tag(i).is_occupied() {
                    let index = self.index.entry_index_ref_mut(i);
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
                let hash = self.entries.load(i).hash;
                let mut slot = hash % self.cap;

                'probing: loop {
                    if self.index.read_tag(slot).is_occupied() {
                        let index = self.index.entry_index_ref_mut(slot);
                        if *index == i {
                            *index -= 1;
                            break 'probing;
                        }
                    }

                    slot = (slot + 1) % self.cap
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
        if count > self.cap / 2 {
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
        unsafe { self.index.set_tags_empty(self.cap) };
        self.deleted = 0;
        self.build_index();
    }

    /// Shrinks or grows the allocated memory space to the specified `new_cap`.
    ///
    /// This method will also reset the index and rebuild it according to the new capacity.
    ///
    /// On error, the map's state will not be affected.
    ///
    /// # Safety
    ///
    /// - Index and entries must be allocated before calling this method.
    ///
    /// - `new_cap` must be greater than `0` and the current length.
    ///
    fn reallocate_reindex(&mut self, new_cap: usize, on_err: OnError) -> Result<(), AllocError> {
        // Important:
        // - This method is designed to be recoverable, the map's state must remain unchanged
        //   until a total success. All or none.
        //
        // - Allocation remains a runtime decision, it can fail regardless of the checking.
        unsafe {
            // The largest layout. Fallible, controlled.
            let new_layout = self.entries.make_layout(new_cap, on_err)?;

            // Already allocated. Infallible, uncontrolled.
            let current_layout = self.entries.make_layout_unchecked(self.cap);

            // Index is much cheaper to deallocate on error.
            let mut new_index = MapIndex::new_unallocated();

            // Fallible, controlled.
            new_index.allocate_uninit(new_cap, on_err)?;

            // Activate index's guard to deallocate new index on sudden drop.
            let index_guard = new_index.guard(new_cap);

            // If the new allocation fails, no deallocation will be done, and the allocated index
            // will be deallocated by the guard, however deallocation is considered infallible.
            self.entries
                .reallocate(current_layout, new_layout, self.len, on_err)?;

            // Infallible, unguarded.
            self.index.deallocate(self.cap);
            debug_assert!(self.index.not_allocated());

            // Deactivate the guard.
            index_guard.deactivate();

            // Update fields.
            self.index = new_index;
            self.cap = new_cap;
            self.deleted = 0;

            // Map's destructor is fully qualified.

            // Initialize control tags and rebuild index.
            self.index.set_tags_empty(new_cap);
            self.build_index();

            // Should be:
            Ok(())
        }
    }

    /// Reclaims deleted slots if suitable or reserves more capacity according to the load factor.
    ///
    /// This method panics when overflow occurs or when allocation fails.
    fn reclaim_or_reserve(&mut self) {
        if self.len < self.cap / 2 {
            // Reclaiming deleted slots without reallocation.
            self.reindex();
        } else {
            // Reallocation.
            let result = if likely(self.cap != 0) {
                let new_cap = self.capacity_next_power_of_two();
                self.reallocate_reindex(new_cap, OnError::NoReturn)
            } else {
                self.allocate::<true>(4, OnError::NoReturn)
            };
            // Hints the compiler that the error branch can be eliminated from the call chain.
            match result {
                Ok(_) => (),
                Err(_) => unsafe { unreachable_unchecked() },
            }
        }
    }

    /// Tries to reserve `additional` capacity.
    ///
    /// All internal calls are checked, with result depends on the error handling context `on_err`.
    fn reserve_additional(&mut self, additional: usize, on_err: OnError) -> Result<(), AllocError> {
        if likely(additional != 0) {
            let extra_cap = Self::allocation_capacity(additional, on_err)?;
            if likely(self.cap != 0) {
                match self.cap.checked_add(extra_cap) {
                    Some(new_cap) => self.reallocate_reindex(new_cap, on_err),
                    None => Err(on_err.overflow()),
                }
            } else {
                self.allocate::<true>(extra_cap, on_err)
            }
        } else {
            Ok(())
        }
    }

    /// Reserves capacity for `additional` more elements.
    ///
    /// The resulting capacity will be equal to `self.capacity() + additional` or _more_ to
    /// maintain the load factor.
    ///
    /// This method is no-op if `additional` is `0`.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Parameters
    ///
    /// - `additional`: The number of additional elements to reserve space for.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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

    /// Tries to reserve capacity for `additional` more elements.
    ///
    /// This method is semantically equivalent to [`OmniMap::reserve`], except that it returns an
    /// error instead of panicking when the allocation fails.
    ///
    /// The resulting capacity will be equal to `self.capacity() + additional` or _more_ to
    /// maintain the load factor.
    ///
    /// This method is no-op if `additional` is `0`.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) on average.
    ///
    /// # Parameters
    ///
    /// - `additional`: The number of additional elements to reserve space for.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::{AllocError, OmniMap};
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
    /// If the key doesn't exist, the retuned `slot` is free for inserting and the value
    /// of `entry` is an **invalid** index.
    ///
    /// # Safety
    ///
    /// Before using `entry`, its value must be checked first with `entry_exists()` method,
    /// because its value can be an invalid index.
    fn find(&self, hash: usize, key: &K) -> FindResult {
        unsafe {
            let mut slot = hash % self.cap;
            // For all valid models: (empty slots exist) -> (unbounded loop can't be infinite).
            loop {
                match self.index.read_tag(slot) {
                    Tag::Empty => return FindResult::just_slot(slot),
                    Tag::Occupied => {
                        let entry = self.index.read_entry_index(slot);
                        if self.entries.load(entry).key == *key {
                            return FindResult { slot, entry };
                        }
                    }
                    Tag::Deleted => {}
                }

                slot = (slot + 1) % self.cap;
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
    /// # Time Complexity
    ///
    /// _O_(1) Amortized.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
        if unlikely(self.len + self.deleted == self.capacity()) {
            self.reclaim_or_reserve();
        }

        let hash = self.make_hash(&key);

        let result = self.find(hash, &key);

        // Key exists, update the value and return the old one.
        if result.entry_exists() {
            let entry = unsafe { self.entries.load_mut(result.entry) };
            let old_val = mem::replace(&mut entry.value, value);
            return Some(old_val);
        };

        unsafe {
            debug_assert!(
                self.index.read_tag(result.slot).is_empty(),
                "Logic error: attempt to overwrite a non-empty slot while inserting"
            );

            self.index.store(result.slot, Tag::Occupied, self.len);
            self.entries.store(self.len, Entry::new(key, value, hash));
        }

        self.len += 1;

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
    /// use omni_map::OmniMap;
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

        let hash = self.make_hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &self.entries.load(result.entry).value };
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
    /// use omni_map::OmniMap;
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

        let hash = self.make_hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &mut self.entries.load_mut(result.entry).value };
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
    /// use omni_map::OmniMap;
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

        let entry = unsafe { self.entries.load_first() };

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
    /// use omni_map::OmniMap;
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

        let entry = unsafe { self.entries.load(self.len - 1) };

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
    /// use omni_map::OmniMap;
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
        let hash = self.make_hash(key);

        let result = self.find(hash, key);

        // Key is found, remove the entry.
        if result.entry_exists() {
            let index = result.entry;

            self.len -= 1;
            self.deleted += 1;

            unsafe {
                let removed = self.entries.read_for_ownership(index).value;
                self.index.store_tag(result.slot, Tag::Deleted);

                if likely(index != self.len) {
                    if SHIFT {
                        // Call order matters.
                        self.decrement_index(index, self.len);
                        self.entries.shift_left(index, self.len - index);
                    } else {
                        let last = self.entries.load(self.len);
                        let swapped = self.find(last.hash, &last.key);
                        self.index.store_entry_index(swapped.slot, index);
                        self.entries.memmove_one(self.len, index);
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
    /// use omni_map::OmniMap;
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
    /// use omni_map::OmniMap;
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
    /// use omni_map::OmniMap;
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
        let entry_ref = unsafe { self.entries.load_first() };

        let result = self.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.len -= 1;
        self.deleted += 1;

        unsafe {
            let removed = self.entries.read_for_ownership(0);
            self.index.store_tag(result.slot, Tag::Deleted);

            // Call order matters.
            self.decrement_index(0, self.len);
            self.entries.shift_left(0, self.len);

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
    /// use omni_map::OmniMap;
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

        let entry_ref = unsafe { self.entries.load(self.len - 1) };

        let result = self.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.len -= 1;
        self.deleted += 1;

        unsafe {
            let removed = self.entries.read_for_ownership(self.len);
            self.index.store_tag(result.slot, Tag::Deleted);

            Some((removed.key, removed.value))
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
    /// use omni_map::OmniMap;
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
        if likely(capacity >= self.len && capacity < self.capacity()) {
            if likely(self.len > 0) {
                // Shrink and keep reserves.
                let new_cap = Self::allocation_capacity_unchecked(capacity);
                match self.reallocate_reindex(new_cap, OnError::NoReturn) {
                    Ok(_) => (),
                    Err(_) => unsafe { unreachable_unchecked() },
                }
            } else {
                self.deallocate();
            }
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
    /// use omni_map::OmniMap;
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
        if likely(self.capacity() > self.len) {
            if likely(self.len > 0) {
                // Shrink and keep reserves.
                let new_cap = Self::allocation_capacity_unchecked(self.len);
                match self.reallocate_reindex(new_cap, OnError::NoReturn) {
                    Ok(_) => (),
                    Err(_) => unsafe { unreachable_unchecked() },
                }
            } else {
                self.deallocate();
            }
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
    /// use omni_map::OmniMap;
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

        unsafe {
            self.entries.drop_initialized(self.len);
            self.index.set_tags_empty(self.cap);
        }

        self.len = 0;
        self.deleted = 0;
    }

    /// Returns an iterator over the current entries.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    fn iter_entries(&self) -> Iter<Entry<K, V>> {
        if self.len == 0 {
            return [].iter();
        };
        unsafe { self.entries.as_slice(self.len).iter() }
    }

    /// Returns a mutable iterator over the entries in the `OmniMap`.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    fn iter_entries_mut(&mut self) -> IterMut<'_, Entry<K, V>> {
        if self.len == 0 {
            return [].iter_mut();
        };
        unsafe { self.entries.as_slice_mut(self.len).iter_mut() }
    }

    /// Returns an iterator over the entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.iter().collect::<Vec<(&i32, &&str)>>(), vec![(&1, &"a"), (&2, &"b")]);
    /// ```
    #[inline]
    pub fn iter(&self) -> IterEntries<'_, K, V> {
        self.iter_entries().map(|entry| (&entry.key, &entry.value))
    }

    /// Returns a mutable iterator over the entries in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
    pub fn iter_mut(&mut self) -> IterEntriesMut<'_, K, V> {
        self.iter_entries_mut()
            .map(|entry| (&entry.key, &mut entry.value))
    }

    /// Returns an iterator over the keys in the `OmniMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
    /// use omni_map::OmniMap;
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
        if self.cap == 0 {
            0.0
        } else {
            (self.len + self.deleted) as f64 / self.cap as f64
        }
    }
}

impl<K, V> Drop for OmniMap<K, V> {
    fn drop(&mut self) {
        if self.cap == 0 {
            return;
        }
        // (Cap > 0) -> entries and index are allocated.
        unsafe {
            // This call is safe even if the length is zero.
            self.entries.drop_initialized(self.len);
            // Infallible, uncontrolled. Already allocated.
            let layout = self.entries.make_layout_unchecked(self.cap);
            self.entries.deallocate(layout);
            self.index.deallocate(self.cap);
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
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::default();
    ///
    /// assert_eq!(map.capacity(), 16);
    /// ```
    #[must_use]
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
    /// use omni_map::OmniMap;
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
        assert!(index < self.len, "Index out of bounds.");
        unsafe { &self.entries.load(index).value }
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
    /// use omni_map::OmniMap;
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
        assert!(index < self.len, "Index out of bounds.");
        unsafe { &mut self.entries.load_mut(index).value }
    }
}

impl<'a, K, V> IntoIterator for &'a OmniMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a V);
    type IntoIter = IterEntries<'a, K, V>;

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
    type IntoIter = IterEntriesMut<'a, K, V>;

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
        if self.len() != other.len() {
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
        // When COMPACT is true, execution takes this path:
        // 1 - Computes allocation capacity according to the current length.
        // 2 - Allocates new instance with initialized control tags.
        // 3 - Clones entries without copying index's data.
        // 4 - Sets the delete counter of the cloned instance to 0.
        // 5 - Builds the index.
        let cap = if COMPACT {
            // len + required reserves.
            Self::allocation_capacity_unchecked(self.len)
        } else {
            self.cap
        };

        let mut instance = Self::new();

        match instance.allocate::<COMPACT>(cap, OnError::NoReturn) {
            Ok(_) => {
                debug_assert!(instance.cap == cap);
                // Clone's destructor is qualified to deallocate.
                unsafe {
                    instance
                        .entries
                        .clone_from(self.entries.pointer(), self.len);
                    instance.len = self.len;
                    // Clone's destructor is qualified to deallocate and drop.
                    if COMPACT {
                        instance.deleted = 0;
                        instance.build_index();
                    } else {
                        instance.deleted = self.deleted;
                        instance.index.copy_from(&self.index, self.cap);
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
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
    #[inline]
    fn clone(&self) -> Self {
        // Return an unallocated instance if the original is unallocated.
        if self.cap == 0 {
            return Self::new();
        }
        self.make_clone::<false>()
    }
}

/// An owning iterator over the entries of an `OmniMap`.
pub struct OmniMapIntoIter<K, V> {
    entries: UnsafeBufferPointer<Entry<K, V>>,
    cap: usize,
    offset: usize,
    end: usize,
}

impl<K, V> Iterator for OmniMapIntoIter<K, V> {
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
    /// [`len`]: OmniMapIntoIter::len()
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<K, V> ExactSizeIterator for OmniMapIntoIter<K, V> {
    /// Returns the number of remaining entries in the iterator.
    #[inline(always)]
    fn len(&self) -> usize {
        self.end - self.offset
    }
}

impl<K, V> Drop for OmniMapIntoIter<K, V> {
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
    type IntoIter = OmniMapIntoIter<K, V>;

    /// Consumes the `OmniMap` and returns an iterator over its entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use omni_map::OmniMap;
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
        let mut iterator = OmniMapIntoIter {
            entries: UnsafeBufferPointer::new(),
            cap: 0,
            end: 0,
            offset: 0,
        };

        // Return an empty iterator if the map is empty.
        if self.len == 0 {
            return iterator;
        }

        // Set the capacity and the length.
        iterator.cap = self.cap;
        iterator.end = self.len;

        // Disable the destructor of the map.
        let mut manual_self = ManuallyDrop::new(self);

        // (Len > 0) -> (capacity > 0) -> entries and index are allocated.
        unsafe {
            // The fields that need deallocation are index and entries.
            // index must be deallocated here and entries shall be deallocated by the iterator.

            // Deallocate the index.
            manual_self.index.deallocate(iterator.cap);

            // Obtain the pointer of the allocated entries and invalidate the original.
            // This will make the iterator the owner of the allocated memory of the entries,
            // and the one responsible for deallocating it.
            iterator.entries = manual_self.entries.invalidate();
        }

        // Done.
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
        // This is safe even if the map is not allocated.
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
        debug_assert!(offset < self.cap);
        unsafe { self.index.read_tag(offset) }
    }

    /// Returns the slot's value at the specified `offset`.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_slot_value(&self, offset: usize) -> usize {
        debug_assert!(offset < self.cap);
        unsafe { self.index.read_entry_index(offset) }
    }

    /// Returns the number of deleted slots.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_deleted(&self) -> usize {
        self.deleted
    }

    /// Returns the number of allocated slots/entries.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_allocated_cap(&self) -> usize {
        self.cap
    }
}
