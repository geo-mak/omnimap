use core::fmt::{Debug, Display};
use core::hash::{Hash, Hasher};
use core::iter::Map;
use core::mem::ManuallyDrop;
use core::ops::{Index, IndexMut};
use core::slice::{Iter, IterMut};
use core::{fmt, mem};

use std::collections::hash_map::DefaultHasher;

use crate::alloc::UnsafeBufferPointer;
use crate::opt::branch_prediction;

struct FindResult {
    slot_index: usize,
    entry_index: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Slot {
    Empty,
    Deleted,
    Occupied(usize),
}

impl Default for Slot {
    #[inline(always)]
    fn default() -> Self {
        Self::Empty
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
    index: UnsafeBufferPointer<Slot>,
    cap: usize,
    len: usize,
    deleted: usize,
}

// Core implementation
impl<K, V> OmniMap<K, V>
where
    K: Eq + Hash,
{
    const MAX_LOAD_FACTOR: f64 = 0.75;
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
    pub fn new() -> Self {
        OmniMap {
            // Unallocated pointers.
            entries: UnsafeBufferPointer::new(),
            index: UnsafeBufferPointer::new(),
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

        OmniMap {
            // Allocate the entries with the specified capacity.
            entries: unsafe { UnsafeBufferPointer::new_allocate(capacity) },
            // Allocate the index with the specified capacity and initialize it with empty slots.
            index: unsafe { UnsafeBufferPointer::new_allocate_default(capacity) },
            cap: capacity,
            len: 0,
            deleted: 0,
        }
    }

    /// Returns the capacity of the `OmniMap`.
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
    #[inline]
    pub fn capacity(&self) -> usize {
        self.cap
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
    #[inline]
    pub fn len(&self) -> usize {
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
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Calculates the hash value for a key.
    #[inline]
    fn make_hash(&self, key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize
    }

    /// Allocates the specified `cap` and fill index with empty slots.
    /// Map's capacity is set to `cap` after calling this method.
    ///
    /// # Safety
    ///
    /// - This method should be called **only** when the map is not allocated.
    ///
    /// - `new_cap` must be greater than `0` and within the range of `isize::MAX` bytes.
    ///
    #[inline]
    fn allocate(&mut self, cap: usize) {
        unsafe {
            self.entries.allocate(cap);
            self.index.allocate(cap);
            // Write empty slots to the new index.
            self.index.memset_default(cap);
        }

        self.cap = cap;
    }

    /// Deallocates the entries and the index without calling `drop` on the initialized entries.
    ///
    /// Fields of capacity, length, and deleted counter will be reset to `0`.
    ///
    /// # Safety
    ///
    /// Index and entries must be allocated before calling this method.
    ///
    #[inline]
    fn deallocate(&mut self) {
        unsafe {
            self.entries.deallocate(self.cap);
            self.index.deallocate(self.cap);
        }

        // Reset fields.
        self.cap = 0;
        self.len = 0;
        self.deleted = 0;
    }

    /// Builds the index of the map according to the current entries and the capacity of the index.
    /// This method should be called **only** after resetting the index with a new capacity.
    fn build_index(&mut self) {
        let enumerator = unsafe { self.entries.as_slice(self.len).iter().enumerate() };
        for (index, entry) in enumerator {
            let mut slot_index = entry.hash % self.cap;
            loop {
                let slot = unsafe { self.index.load_mut(slot_index) };
                match slot {
                    Slot::Empty => {
                        *slot = Slot::Occupied(index);
                        break;
                    }
                    Slot::Occupied(_) => {
                        slot_index = (slot_index + 1) % self.cap;
                    }
                    Slot::Deleted => {
                        unreachable!("Logic error: deleted slot found in the index.");
                    }
                }
            }
        }
    }

    /// Decrements the index of all occupied slots with index value greater than `after` by using
    /// linear search.
    ///
    /// The search domain is `[0, capacity - 1]`.
    const fn decrement_index_linear(&mut self, after: usize) {
        let mut i = 0;
        while i < self.cap {
            let slot = unsafe { self.index.load_mut(i) };
            if let Slot::Occupied(index) = slot {
                if *index > after {
                    *index -= 1
                }
            }
            i += 1
        }
    }

    /// Decrements the index of occupied slots by using the hash value of each entry after `after`
    /// to find its slot.
    ///
    /// The search domain starts from `after` as exclusive bound and ends with `inc_end` as
    /// inclusive upper bound.
    const fn decrement_index_hash(&mut self, after: usize, inc_end: usize) {
        let mut i = after + 1;
        while i <= inc_end {
            let entry = unsafe { self.entries.load(i) };
            let mut slot_index = entry.hash % self.cap;

            'probing: loop {
                let slot = unsafe { self.index.load_mut(slot_index) };
                if let Slot::Occupied(index) = slot {
                    if *index == i {
                        *index -= 1;
                        break 'probing;
                    }
                }

                slot_index = (slot_index + 1) % self.cap
            }

            i += 1;
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

    /// Shrinks or grows the allocated memory space to the specified `new_cap`.
    ///
    /// This method will also reset the index and rebuild it according to the new capacity.
    ///
    /// # Safety
    ///
    /// - Index and entries must be allocated before calling this method.
    ///
    /// - `new_cap` must be greater than `0` and within the range of `isize::MAX` bytes.
    ///
    /// - `new_cap` must be greater than or equal to the current length.
    ///
    #[inline]
    fn reallocate_reindex(&mut self, new_cap: usize) {
        unsafe {
            // Reallocate the entries with the new capacity and copy initialized entries.
            self.entries.reallocate(self.cap, new_cap, self.len);
            // Reallocate the index with the new capacity without copying.
            self.index.reallocate(self.cap, new_cap, 0);
            // Write empty slots to the new index.
            self.index.memset_default(new_cap);
        }

        self.cap = new_cap;
        self.deleted = 0;

        self.build_index();
    }

    /// Resizes map with reindexing if the current load exceeds the load factor.
    fn maybe_grow(&mut self) {
        let load_factor = (self.len + self.deleted) as f64 / self.cap as f64;

        if branch_prediction::unlikely(load_factor > Self::MAX_LOAD_FACTOR) {
            let growth_factor = (self.cap as f64 / Self::MAX_LOAD_FACTOR).ceil() as usize;

            // New capacity must be within the range of `usize` and less than or equal to
            // `isize::MAX`, but error handling is not implemented, because there is no way to
            // deal with such error without making insert, reserve, etc. return a Result.
            let new_cap = growth_factor
                .checked_next_power_of_two()
                .unwrap_or(usize::MAX);

            self.reallocate_reindex(new_cap);
        }
    }

    /// Reserves capacity for `additional` more elements.
    /// The resulting capacity will be equal to `self.capacity() + additional` exactly.
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
    /// map.insert(1, "a");
    ///
    /// // Reserve space for 10 more elements
    /// map.reserve(10);
    ///
    /// // The capacity is now 11
    /// assert_eq!(map.capacity(), 11);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        if branch_prediction::unlikely(additional == 0) {
            return;
        }

        if branch_prediction::unlikely(self.cap == 0) {
            self.allocate(additional);
        } else {
            let new_cap = self.cap.checked_add(additional).unwrap_or(usize::MAX);
            self.reallocate_reindex(new_cap);
        }
    }

    /// Finds the slot of the key in the index.
    ///
    /// # Returns
    ///
    /// `FindResult` with:
    /// - `slot_index`: The index of the slot in the index.
    /// - `entry_index`: `Some(index)` if the key exists, `None` if the key does not exist.
    ///
    fn find(&self, hash: usize, key: &K) -> FindResult {
        debug_assert!(
            self.cap > 0,
            "Logic error: find is called while the map is unallocated"
        );
        let mut slot_index = hash % self.cap;
        let mut step = 0;
        unsafe {
            // Note: It will be an infinite loop, if all slots are occupied and the key doesn't
            // exist, but this is prevented by making capacity the max limit for probing.
            // This case is possible because the user can compact the map anytime.
            while step < self.cap {
                match *self.index.load(slot_index) {
                    Slot::Empty => {
                        return FindResult {
                            slot_index,
                            entry_index: None,
                        };
                    }
                    Slot::Occupied(index) => {
                        if self.entries.load(index).key == *key {
                            return FindResult {
                                slot_index,
                                entry_index: Some(index),
                            };
                        }
                    }
                    Slot::Deleted => {}
                }

                slot_index = (slot_index + 1) % self.cap;
                step += 1;
            }
        }

        // This would the case only if the index is full and the key does not exist.
        FindResult {
            slot_index,
            entry_index: None,
        }
    }

    /// Inserts a key-value pair into the map.
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// This method is semantically equivalent to [`insert`] method, except that it doesn't
    /// allocate capacity automatically.
    ///
    /// This method can be useful if a different capacity management strategy is needed other than
    /// the one used in [`insert`].
    ///
    /// [`insert`]: OmniMap::insert
    ///
    /// # Safety
    ///
    /// Caller must ensure that the map has been initialized and its load factor is less than `1.0`
    /// before calling this method.
    ///
    /// Besides ensuring available capacity, caller must take into account that using very high
    /// load factor can cause severe degradation of lookup performance.
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
    /// // Map must be initialized and has enough capacity before insertion.
    /// map.reserve(2);
    ///
    /// unsafe {
    ///  // When inserting a new key-value pair, None is returned
    ///  map.insert_unchecked(1, "a");
    ///  map.insert_unchecked(2, "b");
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"b"));
    ///
    /// // Update the value for an existing key
    /// let old_value = unsafe {
    ///  map.insert_unchecked(1, "c")
    /// };
    ///
    /// // The old value is returned
    /// assert_eq!(old_value, Some("a"));
    ///
    /// // The value is updated
    /// assert_eq!(map.get(&1), Some(&"c"));
    /// ```
    #[inline]
    pub unsafe fn insert_unchecked(&mut self, key: K, value: V) -> Option<V> {
        let hash = self.make_hash(&key);

        let result = self.find(hash, &key);

        // Key exists, update the value and return the old one.
        if let Some(index) = result.entry_index {
            let old_value: V =
                unsafe { mem::replace(&mut self.entries.load_mut(index).value, value) };
            return Some(old_value);
        };

        // Key does not exist, insert the new key-value pair.
        unsafe {
            // The capacity-management strategy must ensure that the index has empty slots.
            debug_assert!(
                matches!(self.index.load(result.slot_index), Slot::Empty),
                "Logic error: attempt to insert with unempty slot"
            );

            self.index
                .store(result.slot_index, Slot::Occupied(self.len));

            self.entries.store(self.len, Entry::new(key, value, hash));
        }

        self.len += 1;

        // Key was new and inserted.
        None
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
        if branch_prediction::unlikely(self.cap == 0) {
            self.allocate(1);
        } else {
            self.maybe_grow();
        }

        unsafe { self.insert_unchecked(key, value) }
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

        if let Some(index) = self.find(hash, key).entry_index {
            let value = unsafe { &self.entries.load(index).value };
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

        if let Some(index) = self.find(hash, key).entry_index {
            let value = unsafe { &mut self.entries.load_mut(index).value };
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
    pub fn first(&self) -> Option<(&K, &V)> {
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
    pub fn last(&self) -> Option<(&K, &V)> {
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
    #[inline]
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Removes an entry by its `key`.
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
    /// assert_eq!(map.remove(&1), Some("a"));
    ///
    /// assert_eq!(map.len(), 1);
    ///
    /// // Remove a non-existing key
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if self.is_empty() {
            return None;
        }

        let hash = self.make_hash(key);

        let result = self.find(hash, key);

        // Key is found, remove the entry.
        if let Some(index) = result.entry_index {
            self.len -= 1;
            self.deleted += 1;

            let entry = unsafe {
                // Mark the slot as deleted.
                self.index.store(result.slot_index, Slot::Deleted);

                // If the entry is the last one, take it without shifting.
                if branch_prediction::unlikely(index == self.len) {
                    self.entries.take(index)
                } else {
                    self.decrement_index(index, self.len);
                    self.entries.take_shift_left(index, self.len - index)
                }
            };

            return Some(entry.value);
        }

        // Key was not found.
        None
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
            result.entry_index.is_some(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.len -= 1;
        self.deleted += 1;

        let entry = unsafe {
            self.index.store(result.slot_index, Slot::Deleted);
            self.decrement_index(0, self.len);
            self.entries.take_shift_left(0, self.len)
        };

        Some((entry.key, entry.value))
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
            result.entry_index.is_some(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.len -= 1;
        self.deleted += 1;

        let entry = unsafe {
            self.index.store(result.slot_index, Slot::Deleted);
            self.entries.take(self.len)
        };

        Some((entry.key, entry.value))
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
        if branch_prediction::likely(capacity >= self.len && capacity < self.cap) {
            // Zero-count allocation is not allowed.
            // If the length is zero, deallocate the memory.
            if branch_prediction::likely(self.len > 0) {
                self.reallocate_reindex(capacity);
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
        if branch_prediction::likely(self.cap > self.len) {
            // Zero-count allocation is not allowed.
            // If the length is zero, deallocate the memory.
            if branch_prediction::likely(self.len > 0) {
                self.reallocate_reindex(self.len);
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
            self.index.memset_default(self.cap);
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
            self.entries.deallocate(self.cap);
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
    fn clone(&self) -> Self {
        // Return an unallocated instance if the original is unallocated.
        if self.cap == 0 {
            return Self::new();
        }

        // (Capacity > 0) -> entries and index are allocated.
        unsafe {
            OmniMap {
                entries: self.entries.make_clone(self.cap, self.len),
                index: self.index.make_copy(self.cap),
                cap: self.cap,
                len: self.len,
                deleted: self.deleted,
            }
        }
    }
}

impl<K, V> OmniMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
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
    pub fn clone_compact(&self) -> Self {
        if self.is_empty() {
            return Self::new();
        }

        // (Len > 0) -> (capacity > 0) -> entries and index are allocated.
        let mut clone = unsafe {
            OmniMap {
                // Clone the entries with capacity equal to the number of elements.
                entries: self.entries.make_clone(self.len, self.len),
                // NOTE: Index can't be compacted because it's length is equal to the capacity.
                index: UnsafeBufferPointer::new_allocate_default(self.len),
                cap: self.len,
                len: self.len,
                deleted: 0,
            }
        };

        // Reindex the clone.
        clone.build_index();

        // Done.
        clone
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
                self.entries.take(self.offset)
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

            // Deallocate memory space.
            self.entries.deallocate(self.cap);
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
    /// Returns a reference to the internal index.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_index_ptr(&self) -> &UnsafeBufferPointer<Slot> {
        &self.index
    }

    /// Returns the number of deleted slots.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_deleted(&self) -> usize {
        self.deleted
    }
}
