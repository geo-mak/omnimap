use core::fmt::{Debug, Display};
use core::hash::{Hash, Hasher};
use core::iter::Map;
use core::mem::ManuallyDrop;
use core::ops::{Index, IndexMut};
use core::slice::{Iter, IterMut};
use core::{fmt, mem};

use std::collections::hash_map::DefaultHasher;

use crate::alloc::UnsafeBufferPointer;

struct FindResult {
    slot_index: usize,
    entry_index: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
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

/// An immutable iterable view of the key-value pairs in the map.
pub type IterEntries<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> (&K, &V)>;

/// A mutable iterable view of the key-value pairs in the map.
///
/// The keys are immutable, only the values can be modified.
pub type IterEntriesMut<'a, K, V> =
    Map<IterMut<'a, Entry<K, V>>, fn(&mut Entry<K, V>) -> (&K, &mut V)>;

/// A key-value data structure with hash-based indexing and ordered storage of entries, providing
/// fast insertion, deletion, and retrieval of key-value pairs.
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
    // 75% threshold for growing.
    const MAX_LOAD_FACTOR: f64 = 0.75;

    /// Creates a new `OmniMap` with `0` initial capacity.
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

    /// Creates a new `OmniMap` with the specified capacity.
    ///
    /// # Parameters
    ///
    /// - `capacity`: The initial capacity of the map.
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

    /// Returns the number of key-value pairs in the `OmniMap`.
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
        // Allocate the entries and the index with the initial capacity.
        unsafe {
            self.entries.allocate(cap);
            self.index.allocate(cap);
            self.index.memset_default(cap);
        }

        // Update capacity.
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
        // Deallocate the entries and the index.
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

        // Build the index of the current entries.
        for (index, entry) in enumerator {
            let mut slot_index = entry.hash % self.cap;

            // Find the next empty slot and set it to occupied.
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

    #[inline]
    fn decrement_index(&mut self, after: usize) {
        let slots = unsafe { self.index.as_slice_mut(self.cap) };
        for slot in slots {
            if let Slot::Occupied(index) = slot {
                if *index > after {
                    *index -= 1;
                }
            }
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

        // Update the capacity and reset the deleted counter.
        self.cap = new_cap;
        self.deleted = 0;

        // Rebuild the index with the new capacity.
        self.build_index();
    }

    /// Resizes map with reindexing if the current load exceeds the load factor.
    fn maybe_grow(&mut self) {
        let load_factor = (self.len + self.deleted) as f64 / self.cap as f64;

        if load_factor > Self::MAX_LOAD_FACTOR {
            let growth_factor = (self.cap as f64 / Self::MAX_LOAD_FACTOR).ceil() as usize;

            // New capacity must be within the range of `usize` and less than or equal to
            // `isize::MAX`, but error handling is not implemented, because there is no way to
            // deal with such error without making insert, reserve, etc. return a Result.
            let new_cap = growth_factor
                .checked_next_power_of_two()
                .unwrap_or(usize::MAX);

            // Reallocate the entries and index with the new capacity and reindex the map.
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
        if additional == 0 {
            return;
        }

        // The map must be allocated before expanding capacity (Likely).
        if self.cap != 0 {
            // Reallocate the entries and index with the new capacity and reindex the map.
            let new_cap = self.cap.checked_add(additional).unwrap_or(usize::MAX);
            self.reallocate_reindex(new_cap);
        } else {
            // Allocate new capacity.
            self.allocate(additional);
        }
    }

    /// This method will grow the capacity of the map if the current load exceeds the load factor.
    /// If the capacity is zero, it will allocate the initial capacity without reindexing.
    #[inline(always)]
    fn ensure_capacity(&mut self) {
        if self.cap != 0 {
            // This will reindex the map if the capacity is grown.
            self.maybe_grow();
        } else {
            // Allocate initial capacity.
            self.allocate(1);
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
        let mut slot_index = hash % self.cap;
        let mut step = 0;
        unsafe {
            // Note: It will be an infinite loop, if all slots are occupied and the key doesn't 
            // exist, but this is prevented by making capacity the max limit for probing.
            // This case is possible because the user can compact the map anytime.
            while step < self.cap {
                // This is safe because index is always initialized as long the map is allocated.
                match *self.index.load(slot_index) {
                    // Slot is empty, key does not exist.
                    Slot::Empty => {
                        return FindResult {
                            slot_index,
                            entry_index: None,
                        };
                    },
                    // Slot is occupied, check if the key matches.
                    Slot::Occupied(index) => {
                        if self.entries.load(index).key == *key {
                            return FindResult {
                                slot_index,
                                entry_index: Some(index),
                            };
                        }
                    },
                    // Deleted must be treated as occupied, because it might have been occupied
                    // by a key with the same hash, and the searched key might be in the next slot.
                    Slot::Deleted => {},
                }
                // Search further until finding a key match or encountering an empty slot.
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
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // Ensure that the map has enough capacity to insert the new key-value pair.
        self.ensure_capacity();

        let hash = self.make_hash(&key);

        // Find the slot of the key, and possibly the entry index.
        let result = self.find(hash, &key);

        // Key exists, update the value.
        if let Some(index) = result.entry_index {
            let old_value: V = unsafe {
                mem::replace(&mut self.entries.load_mut(index).value, value)
            };
            return Some(old_value)
        };

        // Key does not exist, insert the new key-value pair.
        unsafe {
            // The capacity-management strategy must ensure that the index has empty slots.
            debug_assert!(
                matches!(self.index.load(result.slot_index), Slot::Empty),
                "Logic error: slot is expected to be empty"
            );
            // Update the index.
            self.index.store(result.slot_index, Slot::Occupied(self.len));
            // Insert the new key-value pair.
            self.entries.store(self.len, Entry::new(key, value, hash));
        }

        // Increment the length.
        self.len += 1;
        // Key was new and inserted.
        None
    }

    /// Retrieves a value by its key.
    ///
    /// # Parameters
    ///
    /// - `key`: The key for which to retrieve the value.
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

        // Key exists, return a reference to the value.
        if let Some(index) = self.find(hash, key).entry_index {
            let value = unsafe { &self.entries.load(index).value };
            return Some(value);
        }

        // Key was not found.
        None
    }

    /// Retrieves a mutable reference to a value by its key.
    ///
    /// # Parameters
    ///
    /// - `key`: The key for which to retrieve the mutable reference to the value.
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

        // Key exists, return a mutable reference to the value.
        if let Some(index) = self.find(hash, key).entry_index {
            let value = unsafe { &mut self.entries.load_mut(index).value };
            return Some(value);
        }

        // Key was not found.
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

        // This is safe because the map is not empty.
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

        // This is safe because the map is not empty.
        let entry = unsafe { self.entries.load(self.len - 1) };

        Some((&entry.key, &entry.value))
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Parameters
    ///
    /// - `key`: The key to check for.
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

    /// Removes an entry by its key.
    ///
    /// # Parameters
    ///
    /// - `key`: The key to remove.
    ///
    /// # Returns
    ///
    /// - `Some(value)`: If the key is found and removed.
    ///
    /// - `None`: If the key does not exist.
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
                if index == self.len {
                    self.entries.take_no_shift(index)
                } else {
                    self.decrement_index(index);
                    self.entries
                        .take_shift_left(index, self.len - index)
                }
            };

            // Return the value of the removed entry.
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

        if result.entry_index.is_some() {
            self.len -= 1;
            self.deleted += 1;

            let entry = unsafe {
                self.index.store(result.slot_index, Slot::Deleted);
                self.decrement_index(0);
                self.entries.take_shift_left(0, self.len)
            };

            return Some((entry.key, entry.value));
        };

        // This must be unreachable, the slot must be found.
        unreachable!("Logic error: entry exists, but it has no associated slot in the index.");
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

        if result.entry_index.is_some() {
            self.len -= 1;
            self.deleted += 1;

            let entry = unsafe {
                self.index.store(result.slot_index, Slot::Deleted);
                self.entries.take_no_shift(self.len)
            };

            return Some((entry.key, entry.value));
        }

        // This must be unreachable, the slot must be found.
        unreachable!("Logic error: entry exists, but it has no associated slot in the index.");
    }

    /// Shrinks the capacity of the `OmniMap` to the specified capacity.
    /// In order to take effect, `capacity` must be less than the current capacity
    /// and greater than or equal to the number of elements in the map.
    ///
    /// # Parameters
    ///
    /// - `capacity`: The new capacity of the map.
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
        // Capacity must be less than the current capacity and greater than or equal to the number
        // of elements.
        if capacity >= self.len && capacity < self.cap {
            // Zero-count allocation is not allowed.
            // If the length is zero, deallocate the memory.
            if self.len > 0 {
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
        // Capacity must be greater than the number of elements.
        if self.cap > self.len {
            // Zero-count allocation is not allowed.
            // If the length is zero, deallocate the memory.
            if self.len > 0 {
                self.reallocate_reindex(self.len);
            } else {
                self.deallocate();
            }
        }
    }

    /// Clears the map, removing all key-value pairs.
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
            // Range: [0, len - 1]
            self.entries.drop_initialized(self.len);
            // Range: [0, cap - 1]
            self.index.memset_default(self.cap);
        }

        // Reset the length and the deleted counter.
        self.len = 0;
        self.deleted = 0;
    }

    /// Returns an iterator over the entries in the `OmniMap`.
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

    /// Returns an iterator over the key-value pairs in the `OmniMap`.
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

    /// Returns a mutable iterator over the key-value pairs in the `OmniMap`.
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

    /// Returns the current load factor of the `OmniMap` as a ratio.
    #[inline]
    pub fn current_load(&self) -> f64 {
        if self.cap == 0 {
            return 0.0;
        }
        (self.len + self.deleted) as f64 / self.cap as f64
    }
}

impl<K, V> Drop for OmniMap<K, V> {
    fn drop(&mut self) {
        if self.cap == 0 {
            return;
        }
        // Cap > 0 implies that the entries and index are allocated.
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
        Self::with_capacity(16)
    }
}

impl<K, V> Index<usize> for OmniMap<K, V> {
    type Output = V;

    /// Returns immutable reference to the value at the specified index.
    ///
    /// # Parameters
    ///
    /// - `index`: The index of the value to retrieve.
    ///
    /// # Returns
    ///
    /// A reference to the value at the specified index.
    ///
    /// # Panics
    ///
    /// If the index is out of bounds.
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
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len, "Index out of bounds.");
        unsafe { &self.entries.load(index).value }
    }
}

impl<K, V> IndexMut<usize> for OmniMap<K, V> {
    /// Returns mutable reference to the value at the specified index.
    ///
    /// # Parameters
    ///
    /// - `index`: The index of the value to retrieve.
    ///
    /// # Returns
    ///
    /// A mutable reference to the value at the specified index.
    ///
    /// # Panics
    ///
    /// If the index is out of bounds.
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
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
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

    /// Returns an iterator over the key-value pairs in the `OmniMap`.
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

    /// Returns a mutable iterator over the key-value pairs in the `OmniMap`.
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
        // Return an unallocated clone if the original is unallocated.
        if self.cap == 0 {
            return Self::new();
        }

        // Capacity > 0 => entries and index are allocated.
        unsafe {
            OmniMap {
                entries: self.entries.make_clone(self.cap, self.len),
                index: self.index.make_clone(self.cap, self.cap),
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
    /// Creates a compact clone of the current instance.
    ///
    /// This method creates a clone of the `OmniMap` where the capacity of the internal
    /// storage is reduced to fit the current number of elements. This can help reduce
    /// memory usage if the map has a lot of unused capacity.
    ///
    /// # Returns
    ///
    /// A new `OmniMap` instance with the same elements as the original, but with a
    /// capacity equal to the number of elements.
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
        // Return an empty clone if the original is empty.
        if self.is_empty() {
            return Self::new();
        }

        // Len > 0 => capacity > 0 => entries and index are allocated.
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

/// An owning iterator over the key-value pairs of an `OmniMap`.
pub struct OmniMapIntoIter<K, V> {
    entries: UnsafeBufferPointer<Entry<K, V>>,
    cap: usize,
    len: usize,
    index: usize,
}

impl<K, V> Iterator for OmniMapIntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // self.index < self.len => len > 0 => pointer is not null.
        if self.index < self.len {
            let item = unsafe {
                // Safety: The destructor of the iterator must not call drop on this value,
                // or it will be double-drop.
                self.entries.take_no_shift(self.index)
            };
            self.index += 1;
            Some((item.key, item.value))
        } else {
            None
        }
    }
}

impl<K, V> Drop for OmniMapIntoIter<K, V> {
    fn drop(&mut self) {
        if self.entries.is_null() {
            return;
        }

        unsafe {
            // self.index < self.len => len > 0 && the iterator is not exhausted.
            if self.index < self.len {
                // Drop the remaining entries.
                self.entries.drop_range(self.index..self.len);
            }

            // Deallocate memory space.
            self.entries.deallocate(self.cap);
        }
    }
}

impl<K, V> IntoIterator for OmniMap<K, V> {
    type Item = (K, V);
    type IntoIter = OmniMapIntoIter<K, V>;

    /// Consumes the `OmniMap` and returns an iterator over its key-value pairs.
    ///
    /// # Returns
    ///
    /// An iterator that yields key-value pairs in the order they were inserted.
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
            len: 0,
            index: 0,
        };

        // Return an empty iterator if the map is empty.
        if self.len == 0 {
            return iterator;
        }

        // Set the capacity and the length.
        iterator.cap = self.cap;
        iterator.len = self.len;

        // Disable the destructor of the map.
        let mut manual_self = ManuallyDrop::new(self);

        // Len > 0 => capacity > 0 => entries and index are allocated.
        unsafe {
            // Obtain the pointer of the allocated entries and invalidate the original.
            // This will make the iterator the owner of the allocated memory of the entries,
            // and the one responsible for deallocating it.
            iterator.entries = manual_self.entries.invalidate();

            // Deallocate the index.
            manual_self.index.deallocate(iterator.cap);
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
