use core::borrow::Borrow;
use core::cmp::max;
use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::hint::unreachable_unchecked;
use core::iter::Map;
use core::mem::ManuallyDrop;
use core::ops::{Index, IndexMut};
use core::slice::{Iter, IterMut};
use core::{fmt, mem};

use crate::core::{CoreMap, Entry};
use crate::index::Tag;
use crate::mem::error::{MemoryError, OnError};
use crate::mem::pointers::UnmanagedPointer;
use crate::opt::OnDrop;
use crate::opt::branch_hints::unlikely;

/// An immutable iterable view of the entries in the map.
pub type EntriesIterator<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> (&K, &V)>;

/// A mutable iterable view of the entries in the map.
///
/// The keys are immutable, only the values can be modified.
pub type EntriesIteratorMut<'a, K, V> =
    Map<IterMut<'a, Entry<K, V>>, fn(&mut Entry<K, V>) -> (&K, &mut V)>;

/// An immutable iterable view of the keys in the map.
pub type KeysIterator<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> &K>;

/// An immutable iterable view of the values in the map.
pub type ValuesIterator<'a, K, V> = Map<Iter<'a, Entry<K, V>>, fn(&Entry<K, V>) -> &V>;

/// A mutable iterable view of the values in the map.
pub type ValuesIteratorMut<'a, K, V> =
    Map<IterMut<'a, Entry<K, V>>, fn(&mut Entry<K, V>) -> &mut V>;

/// A key-value data structure with hash-based indexing and ordered storage of entries, providing
/// fast insertion, deletion, and retrieval of entries.
///
/// It offers intuitive and ergonomic APIs inspired by hash maps and vectors, with the added
/// benefit of predictable iteration order and stable indices.
pub struct OmniMap<K, V> {
    core: CoreMap<K, V>,
}

impl<K, V> Drop for OmniMap<K, V> {
    fn drop(&mut self) {
        if self.core.cap == 0 {
            return;
        }

        unsafe {
            // This call is safe even if the length is zero.
            self.core.drop_initialized();
            self.core.release();
        }
    }
}

impl<K, V> Default for OmniMap<K, V> {
    /// Creates a new instance with the default capacity.
    /// The default capacity is set to `16`, with 14 as useable capacity.
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
    /// assert_eq!(map.capacity(), 14);
    /// ```
    #[inline]
    fn default() -> Self {
        match CoreMap::new_acquire_init(Self::DEFAULT_CAPACITY, OnError::Panic) {
            Ok(data) => Self { core: data },
            Err(_) => unsafe { unreachable_unchecked() },
        }
    }
}

impl<K, V> OmniMap<K, V> {
    const DEFAULT_CAPACITY: usize = 16;

    /// Returns a new instance without allocated capacity.
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
            core: CoreMap::new(),
        }
    }

    /// Creates a new instance with the specified `capacity`.
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

        let cap = match CoreMap::<K, V>::allocation_capacity(capacity, OnError::Panic) {
            Ok(cap) => cap,
            Err(_) => unsafe { unreachable_unchecked() },
        };

        match CoreMap::new_acquire_init(cap, OnError::Panic) {
            Ok(core) => OmniMap { core },
            Err(_) => unsafe { unreachable_unchecked() },
        }
    }

    /// Returns the remaining usable capacity of the map.
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
    /// assert_eq!(map.capacity(), 14);
    ///
    /// let map: OmniMap<i32, &str> = OmniMap::with_capacity(10);
    /// assert_eq!(map.capacity(), 10);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        self.core.free
    }

    /// Returns the number of entries in the map.
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
        self.core.len
    }

    /// Checks if the map is empty.
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
        self.core.len == 0
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
    /// // The allocated capacity with first insert is 3.
    /// map.insert(1, "a");
    /// assert_eq!(map.capacity(), 2);
    ///
    /// // Reserve space for 10 more elements
    /// map.reserve(10);
    ///
    /// // The capacity is now 13.
    /// assert_eq!(map.capacity(), 13);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        match self.core.acquire_additional(additional, OnError::Panic) {
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
    /// use omnimap::{MemoryError, OmniMap};
    ///
    /// let mut map = OmniMap::new();
    ///
    /// // The initial capacity with first insert is 3.
    /// map.insert(1, "a");
    ///
    /// // Try reserve space for very large number of elements.
    /// let mut result = map.try_reserve(usize::MAX);
    ///
    /// // Result must be error.
    /// assert!(matches!(result.err().unwrap(), MemoryError::LayoutErr));
    ///
    /// // The free capacity remains 2.
    /// assert_eq!(map.capacity(), 2);
    ///
    /// // Reserve space for 10 more elements
    /// result = map.try_reserve(10);
    ///
    /// assert!(result.is_ok());
    ///
    /// // The capacity is now 13.
    /// assert_eq!(map.capacity(), 13);
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), MemoryError> {
        self.core.acquire_additional(additional, OnError::ReturnErr)
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

        let entry = unsafe { self.core.entries.as_ref() };

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

        let entry = unsafe { self.core.entries.reference(self.core.len - 1) };

        Some((&entry.key, &entry.value))
    }

    /// Shrinks the capacity of the map to the specified capacity.
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
    /// // Insert 2 elements.
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.capacity(), 8);
    ///
    /// // Shrink the capacity to 5.
    /// map.shrink_to(5);
    ///
    /// assert_eq!(map.capacity(), 3);
    /// ```
    pub fn shrink_to(&mut self, capacity: usize) {
        let current_len = self.core.len;

        let shrinking_cap = max(current_len, capacity);

        if shrinking_cap < self.core.usable_capacity() {
            // Safety: The core has an allocated memory.

            if shrinking_cap == 0 {
                // Safety: The shrinking capacity = len = 0.
                unsafe {
                    self.core.release();
                    self.core.cap = 0;
                    self.core.free = 0;
                };

                return;
            }

            // Safety: The shrinking capacity is less than the usable capacity.
            let new_cap = unsafe { CoreMap::<K, V>::allocation_capacity_unchecked(shrinking_cap) };

            let result = if current_len == 0 {
                unsafe { self.core.adjust_unused_layout(new_cap, OnError::Panic) }
            } else {
                unsafe { self.core.adjust_used_layout(new_cap, OnError::Panic) }
            };

            match result {
                Ok(_) => (),
                Err(_) => unsafe { unreachable_unchecked() },
            }
        }
    }

    /// Shrinks the capacity of the map to fit its current length.
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
    /// assert_eq!(map.capacity(), 10);
    ///
    /// // Insert some elements
    ///  map.insert(1, "a");
    ///  map.insert(2, "b");
    ///
    /// // Shrink the capacity to fit the current length.
    /// map.shrink_to_fit();
    ///
    /// assert_eq!(map.capacity(), 0);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        let current_len = self.core.len;

        if current_len < self.core.usable_capacity() {
            // Safety: The core has an allocated memory
            if current_len == 0 {
                unsafe {
                    self.core.release();
                    self.core.cap = 0;
                    self.core.free = 0;
                };

                return;
            }

            let new_cap = unsafe { CoreMap::<K, V>::allocation_capacity_unchecked(current_len) };

            match unsafe { self.core.adjust_used_layout(new_cap, OnError::Panic) } {
                Ok(_) => (),
                Err(_) => unsafe { unreachable_unchecked() },
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

        let protected_clear = OnDrop::set_on(self, |current| {
            unsafe { current.core.index.reset_tags(current.core.cap) };
            current.core.len = 0;
            current.core.free = current.core.usable_capacity();
        });

        unsafe {
            protected_clear.arg.core.drop_initialized();
        }
    }

    /// Returns an iterator over the entries in the map.
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
        self.core
            .iter_entries()
            .map(|entry| (&entry.key, &entry.value))
    }

    /// Returns a mutable iterator over the entries in the map.
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
        self.core
            .iter_entries_mut()
            .map(|entry| (&entry.key, &mut entry.value))
    }

    /// Returns an iterator over the keys in the map.
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
    pub fn iter_keys(&self) -> KeysIterator<'_, K, V> {
        self.core.iter_entries().map(|entry| &entry.key)
    }

    /// Returns an iterator over the values in the map.
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
    pub fn iter_values(&self) -> ValuesIterator<'_, K, V> {
        self.core.iter_entries().map(|entry| &entry.value)
    }

    /// Returns a mutable iterator over the values.
    ///
    /// # Examples
    ///
    /// ```
    /// use omnimap::OmniMap;
    ///
    /// let mut map = OmniMap::new();
    ///
    /// map.insert(1, 1);
    /// map.insert(2, 2);
    ///
    /// assert_eq!(map.iter_values_mut().collect::<Vec<&mut u8>>(), vec![&1, &2]);
    /// ```
    #[inline]
    pub fn iter_values_mut(&mut self) -> ValuesIteratorMut<'_, K, V> {
        self.core.iter_entries_mut().map(|entry| &mut entry.value)
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
    #[inline]
    fn index(&self, index: usize) -> &V {
        assert!(index < self.core.len, "Index out of bounds.");
        unsafe { &self.core.entries.reference(index).value }
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
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut V {
        assert!(index < self.core.len, "Index out of bounds.");
        unsafe { &mut self.core.entries.reference_mut(index).value }
    }
}

impl<K, V> OmniMap<K, V>
where
    K: Clone,
    V: Clone,
{
    fn make_clone(&self) -> Self {
        let current_cap = self.core.cap;
        let current_len = self.core.len;

        let core = match CoreMap::new_acquire_init(current_cap, OnError::Panic) {
            Ok(instance) => instance,
            Err(_) => unsafe { unreachable_unchecked() },
        };

        debug_assert!(core.cap == self.core.cap);
        debug_assert!(core.len == 0);

        // On panic, instance's memory will be deallocated.
        let mut instance = Self { core };

        // Unwind-safe. On panic, cloned items will be dropped.
        unsafe {
            instance
                .core
                .entries
                .clone_from(self.core.entries.as_ptr(), current_len)
        }

        instance.core.len = current_len;

        // Same index-state.
        instance.core.free = self.core.free;

        unsafe { instance.core.index.copy_from(&self.core.index, current_cap) }

        instance
    }

    fn make_compact_clone(&self) -> Self {
        let current_len = self.core.len;

        let compact_cap = unsafe { CoreMap::<K, V>::allocation_capacity_unchecked(current_len) };

        let core = match CoreMap::new_acquire_init(compact_cap, OnError::Panic) {
            Ok(instance) => instance,
            Err(_) => unsafe { unreachable_unchecked() },
        };

        debug_assert!(core.cap == compact_cap);
        debug_assert!(core.len == 0);

        // On panic, instance's memory will be deallocated.
        let mut instance = Self { core };

        // Unwind-safe. On panic, cloned items will be dropped.
        unsafe {
            instance
                .core
                .entries
                .clone_from(self.core.entries.as_ptr(), current_len)
        }

        instance.core.len = current_len;

        // New index with usable cap set to len.
        instance.core.free = 0;
        instance.core.build_index();
        instance
    }

    /// Returns a compact clone of the current instance.
    ///
    /// This method creates a clone of the map where the capacity of the internal
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
    /// assert_eq!(compact_clone.capacity(), 0);
    ///
    /// assert_eq!(compact_clone.get(&1), Some(&"a"));
    /// assert_eq!(compact_clone.get(&2), Some(&"b"));
    /// ```
    #[inline]
    pub fn clone_compact(&self) -> Self {
        if self.is_empty() {
            return Self::new();
        }
        self.make_compact_clone()
    }
}

impl<K, V> Clone for OmniMap<K, V>
where
    K: Clone,
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
        if self.core.cap == 0 {
            return Self::new();
        }
        self.make_clone()
    }
}

impl<K, V> OmniMap<K, V>
where
    K: Hash + Eq,
{
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
        if unlikely(self.core.free == 0) {
            self.core.reclaim_or_acquire();
        }

        let hash = CoreMap::<K, V>::make_hash(&key);

        let result = self.core.find(hash, &key);

        if result.entry_exists() {
            let entry = unsafe { self.core.entries.reference_mut(result.entry) };
            let old_val = mem::replace(&mut entry.value, value);
            return Some(old_val);
        };

        unsafe {
            debug_assert!(
                self.core.index.load_tag(result.slot).is_free(),
                "Logic error: attempt to overwrite a non-empty slot while inserting"
            );

            self.core
                .entries
                .store(self.core.len, Entry::new(key, value, hash));

            self.core.index.store(result.slot, Tag::Used, self.core.len);
        }

        self.core.len += 1;
        self.core.free -= 1;

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
    pub fn get<B>(&self, key: &B) -> Option<&V>
    where
        K: Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        if self.is_empty() {
            return None;
        }

        let hash = CoreMap::<K, V>::make_hash(&key);

        let result = self.core.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &self.core.entries.reference(result.entry).value };
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
    pub fn get_mut<B>(&mut self, key: &B) -> Option<&mut V>
    where
        K: Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        if self.is_empty() {
            return None;
        }

        let hash = CoreMap::<K, V>::make_hash(&key);

        let result = self.core.find(hash, key);

        if result.entry_exists() {
            let value = unsafe { &mut self.core.entries.reference_mut(result.entry).value };
            return Some(value);
        }

        None
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
    pub fn contains_key<B>(&self, key: &B) -> bool
    where
        K: Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        self.get(key).is_some()
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
    pub fn shift_remove<B>(&mut self, key: &B) -> Option<V>
    where
        K: Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        if self.is_empty() {
            return None;
        }
        self.core.remove_entry::<B, true>(key)
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
    pub fn swap_remove<B>(&mut self, key: &B) -> Option<V>
    where
        K: Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        if self.is_empty() {
            return None;
        }
        self.core.remove_entry::<B, false>(key)
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
        let entry_ref = unsafe { self.core.entries.as_ref() };

        let result = self.core.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.core.len -= 1;

        unsafe {
            self.core.index.store_tag(result.slot, Tag::Discarded);
            let removed = self.core.entries.read_for_ownership(0);

            // Call order matters.
            self.core.decrement_index(0, self.core.len);
            self.core.entries.shift_left(0, self.core.len);

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

        let entry_ref = unsafe { self.core.entries.reference(self.core.len - 1) };

        let result = self.core.find(entry_ref.hash, &entry_ref.key);

        debug_assert!(
            result.entry_exists(),
            "Logic error: entry exists, but it has no associated slot in the index"
        );

        self.core.len -= 1;

        unsafe {
            self.core.index.store_tag(result.slot, Tag::Discarded);
            let removed = self.core.entries.read_for_ownership(self.core.len);

            Some((removed.key, removed.value))
        }
    }
}

impl<K, V> PartialEq for OmniMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.core.len != other.len() {
            return false;
        }
        self.iter()
            .all(|(key, value)| other.get(key).is_some_and(|v| *value == *v))
    }
}

impl<'a, K, V> IntoIterator for &'a OmniMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = EntriesIterator<'a, K, V>;

    /// Returns an iterator over the entries.
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut OmniMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = EntriesIteratorMut<'a, K, V>;

    /// Returns a mutable iterator over the entries.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An owning iterator over the entries of the map.
pub struct OmniMapIterator<K, V> {
    entries: UnmanagedPointer<Entry<K, V>>,
    cap: usize,
    offset: usize,
    end: usize,
}

impl<K, V> OmniMapIterator<K, V> {
    #[inline]
    const fn new() -> Self {
        Self {
            entries: UnmanagedPointer::new(),
            cap: 0,
            end: 0,
            offset: 0,
        }
    }
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
            let layout = self.entries.layout_unchecked_of(self.cap);
            self.entries.release(layout);
        }
    }
}

impl<K, V> IntoIterator for OmniMap<K, V> {
    type Item = (K, V);
    type IntoIter = OmniMapIterator<K, V>;

    /// Consumes the instance and returns an iterator over its entries.
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
        if self.core.len == 0 {
            return OmniMapIterator::new();
        }

        let mut iterator = OmniMapIterator {
            entries: UnmanagedPointer::new(),
            cap: self.core.cap,
            end: self.core.len,
            offset: 0,
        };

        let mut manual_self = ManuallyDrop::new(self);

        // The fields that need deallocation are index and entries.
        // index must be deallocated here and entries shall be deallocated by the iterator.
        unsafe {
            manual_self.core.index.release(iterator.cap);
            iterator.entries = manual_self.core.entries.duplicate();
        }

        iterator
    }
}

impl<K, V> Debug for OmniMap<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> Display for OmniMap<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        // This call is safe even if the map is not allocated.
        for entry in self.core.iter_entries() {
            writeln!(f, "    {}: {}", entry.key, entry.value)?;
        }
        write!(f, "}}")
    }
}

/// Development and testing methods that are not available in release builds.
#[cfg(test)]
impl<K, V> OmniMap<K, V> {
    /// Returns the the total allocated capacity including the _unusable_ capacity.
    #[inline(always)]
    pub(crate) const fn debug_allocated_capacity(&self) -> usize {
        self.core.cap
    }

    /// Returns the total usable capacity of the map.
    #[inline(always)]
    pub(crate) const fn debug_usable_capacity(&self) -> usize {
        self.core.usable_capacity()
    }

    /// Returns the tag's value of the slot at the specified `offset`.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_tag(&self, offset: usize) -> Tag {
        debug_assert!(offset < self.core.cap);
        unsafe { self.core.index.load_tag(offset) }
    }

    /// Returns the slot's value at the specified `offset`.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_slot_value(&self, offset: usize) -> usize {
        debug_assert!(offset < self.core.cap);
        unsafe { self.core.index.load_entry_index(offset) }
    }

    /// Returns the number of deleted slots.
    ///
    /// This method is used for testing purposes only and not available in release builds.
    pub(crate) fn debug_deleted(&self) -> usize {
        self.core.usable_capacity() - (self.core.free + self.core.len)
    }
}
