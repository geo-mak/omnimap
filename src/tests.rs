#[cfg(test)]
mod map_tests {
    use crate::map::{OmniMap, OmniMapIntoIter, Slot};

    #[test]
    fn test_map_new() {
        let map: OmniMap<u8, &str> = OmniMap::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 0);
    }

    #[test]
    fn test_map_new_with_capacity() {
        let map: OmniMap<u8, &str> = OmniMap::with_capacity(10);

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 10);
    }

    #[test]
    fn test_map_current_load() {
        // New map with zero capacity.
        let mut map = OmniMap::new();

        // Empty map.
        assert_eq!(map.load_factor(), 0.0);

        map.insert(1, 2);

        // Full capacity 1.
        assert_eq!(map.load_factor(), 1.0);

        map.insert(2, 3);

        // Full capacity 2.
        assert_eq!(map.load_factor(), 1.0);

        map.insert(3, 4);

        // 3/4 of new capacity 4, which is exactly the threshold.
        assert_eq!(map.load_factor(), 0.75);

        map.insert(4, 5);

        // Full capacity 4.
        assert_eq!(map.load_factor(), 1.0);

        map.insert(5, 6);

        // 5/8 of new capacity 8.
        assert_eq!(map.load_factor(), 0.625);
    }

    #[test]
    fn test_map_new_default() {
        let map: OmniMap<u8, &str> = OmniMap::default();

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 16);
    }
    
    #[test]
    fn test_map_insert_get_unchecked() {
        let mut map = OmniMap::new();

        map.reserve(3);

        // Access when the map is empty must return None.
        assert_eq!(map.get(&1), None);

        unsafe {
            assert_eq!(map.insert_unchecked(1, 2), None);
            assert_eq!(map.insert_unchecked(2, 3), None);
            assert_eq!(map.insert_unchecked(3, 4), None);
        }

        // Map state.
        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 3);

        // Check values.
        assert_eq!(map.get(&1), Some(&2));
        assert_eq!(map.get(&2), Some(&3));
        assert_eq!(map.get(&3), Some(&4));
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "Logic error: find is called while the map is unallocated")]
    fn test_map_insert_get_unchecked_new() {
        let mut map = OmniMap::new();
        unsafe {
            // find must panic.
            map.insert_unchecked(1, 2);
        }
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "Logic error: attempt to insert with unempty slot")]
    fn test_map_insert_get_unchecked_full() {
        let mut map = OmniMap::new();

        map.reserve(1);

        unsafe {
            assert_eq!(map.insert_unchecked(1, 2), None);

            // The map is 100% full.
            assert_eq!(map.load_factor(), 1.0);

            // No room for it, should panic.
            assert_eq!(map.insert_unchecked(2, 3), None);
        }
    }

    #[test]
    fn test_map_insert_get() {
        let mut map = OmniMap::new();

        // Access when the map is empty must return None.
        assert_eq!(map.get(&1), None);

        assert_eq!(map.insert(1, 2), None);
        assert_eq!(map.insert(2, 3), None);
        assert_eq!(map.insert(3, 4), None);

        // Map state.
        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        // Check values.
        assert_eq!(map.get(&1), Some(&2));
        assert_eq!(map.get(&2), Some(&3));
        assert_eq!(map.get(&3), Some(&4));
    }

    #[test]
    fn test_map_insert_update() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Update the value for keys 1 and 2.
        assert_eq!(map.insert(1, 22), Some(2));
        assert_eq!(map.insert(2, 33), Some(3));

        // Values must be updated.
        assert_eq!(map.get(&1), Some(&22));
        assert_eq!(map.get(&2), Some(&33));

        // Key 3 must remain the same.
        assert_eq!(map.get(&3), Some(&4));
    }

    #[test]
    fn test_map_access_get_mut() {
        let mut map = OmniMap::new();

        // Access when the map is empty must return None.
        assert_eq!(map.get_mut(&1), None);

        map.insert(1, 1);

        if let Some(value) = map.get_mut(&1) {
            *value = 10;
        }

        assert_eq!(map.get(&1), Some(&10));
    }

    #[test]
    fn test_map_access_index() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        assert_eq!(map[0], 2);
        assert_eq!(map[1], 3);
        assert_eq!(map[2], 4);

        // Remove the first item.
        map.pop_front();

        // The first item now must be the second item.
        assert_eq!(map[0], 3);

        // The second item now must be the third item.
        assert_eq!(map[1], 4);
    }

    #[test]
    fn test_map_access_index_mut() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i);
        }

        map[0] = 10;
        map[1] = 20;
        map[2] = 30;

        assert_eq!(map[0], 10);
        assert_eq!(map[1], 20);
        assert_eq!(map[2], 30);
    }

    #[test]
    #[should_panic(expected = "Index out of bounds")]
    fn test_map_access_index_out_of_bounds() {
        let mut map = OmniMap::new();

        map.insert(1, 1);

        // ok.
        assert_eq!(map[0], 1);

        // This must panic.
        let _ = map[1];
    }

    #[test]
    fn test_map_access_get_first() {
        let mut map = OmniMap::new();

        // Access when the map is empty must return None.
        assert_eq!(map.first(), None);

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        assert_eq!(map.first(), Some((&1, &2)));
    }

    #[test]
    fn test_map_access_get_last() {
        let mut map = OmniMap::new();

        // Access when the map is empty must return None.
        assert_eq!(map.last(), None);

        for i in 1..4 {
            map.insert(i, i);
        }

        assert_eq!(map.last(), Some((&3, &3)));
    }

    #[test]
    fn test_map_contains_key() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Keys exist.
        assert!(map.contains_key(&1));
        assert!(map.contains_key(&2));
        assert!(map.contains_key(&3));

        // Key does not exist.
        assert!(!map.contains_key(&4));
    }

    #[test]
    fn test_map_pop_front() {
        let mut map = OmniMap::new();

        // Pop when the map is empty must return None.
        assert_eq!(map.pop_front(), None);

        // First item.
        map.insert(1, 2);

        // Must return the only item in the map.
        let (key, value) = map.pop_front().unwrap();

        assert_eq!(key, 1);
        assert_eq!(value, 2);
        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 1);

        unsafe {
            assert_eq!(*map.debug_index_ptr().load(0), Slot::Deleted);
        }

        assert_eq!(map.capacity(), 1);

        // Must return None, because the map is empty.
        assert_eq!(map.pop_front(), None);

        // Insert new items.
        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Now, the map must expand its capacity reset the deleted counter.
        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        // Pop the first item.
        assert_eq!(map.pop_front(), Some((1, 2)));

        // Map state at this point.
        assert_eq!(map.len(), 2);
        assert_eq!(map.debug_deleted(), 1);
        assert_eq!(map.capacity(), 4);

        // Index state at this point.
        let mut deleted = 0;
        let mut occupied = 0;
        let mut empty = 0;

        unsafe {
            for i in 0..map.capacity() {
                match map.debug_index_ptr().load(i) {
                    Slot::Deleted => {
                        deleted += 1;
                    }
                    Slot::Occupied(_) => {
                        occupied += 1;
                    }
                    Slot::Empty => {
                        empty += 1;
                    }
                }
            }
        }

        // Expected index state at this point.
        assert_eq!(deleted, 1);
        assert_eq!(occupied, 2);
        assert_eq!(empty, 1);

        // Expected values at this point.
        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), Some(&3));
        assert_eq!(map.get(&3), Some(&4));
    }

    #[test]
    fn test_map_pop() {
        let mut map = OmniMap::new();

        // Pop when the map is empty must return None.
        assert_eq!(map.pop(), None);

        // Last item.
        map.insert(1, 2);

        // Must return the only item in the map.
        let (key, value) = map.pop().unwrap();

        assert_eq!(key, 1);
        assert_eq!(value, 2);
        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 1);

        unsafe {
            assert_eq!(*map.debug_index_ptr().load(0), Slot::Deleted);
        }

        assert_eq!(map.capacity(), 1);

        // Must return None, because the map is empty.
        assert_eq!(map.pop(), None);

        // Insert new items.
        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Now, the map must expand its capacity reset the deleted counter.
        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        // Pop the last item.
        assert_eq!(map.pop(), Some((3, 4)));

        // Map state at this point.
        assert_eq!(map.len(), 2);
        assert_eq!(map.debug_deleted(), 1);
        assert_eq!(map.capacity(), 4);

        // Index state at this point.
        let mut deleted = 0;
        let mut occupied = 0;
        let mut empty = 0;

        unsafe {
            for i in 0..map.capacity() {
                match map.debug_index_ptr().load(i) {
                    Slot::Deleted => {
                        deleted += 1;
                    }
                    Slot::Occupied(_) => {
                        occupied += 1;
                    }
                    Slot::Empty => {
                        empty += 1;
                    }
                }
            }
        }

        // Expected index state at this point.
        assert_eq!(deleted, 1);
        assert_eq!(occupied, 2);
        assert_eq!(empty, 1);

        // Expected values at this point.
        assert_eq!(map.get(&1), Some(&2));
        assert_eq!(map.get(&2), Some(&3));
        assert_eq!(map.get(&3), None);
    }

    #[test]
    fn test_map_remove_existing_key() {
        let mut map = OmniMap::new();

        map.insert(1, 2);

        // Remove the only item.
        assert_eq!(map.remove(&1), Some(2));

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 1);

        unsafe {
            assert_eq!(*map.debug_index_ptr().load(0), Slot::Deleted);
        }

        assert_eq!(map.capacity(), 1);

        // Must return None, because the map is empty.
        assert_eq!(map.remove(&1), None);

        // Insert new items.
        for i in 1..5 {
            map.insert(i, i + 1);
        }

        // Now, the map must have expanded its capacity and reset the deleted counter.
        assert_eq!(map.len(), 4);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        // Remove the second item (key "2").
        assert_eq!(map.remove(&2), Some(3));

        // Map state at this point.
        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 1);
        assert_eq!(map.capacity(), 4);

        // Index state at this point.
        let mut deleted = 0;
        let mut occupied = 0;
        let mut empty = 0;

        unsafe {
            for i in 0..map.capacity() {
                match map.debug_index_ptr().load(i) {
                    Slot::Deleted => {
                        deleted += 1;
                    }
                    Slot::Occupied(_) => {
                        occupied += 1;
                    }
                    Slot::Empty => {
                        empty += 1;
                    }
                }
            }
        }

        // Expected index state at this point.
        assert_eq!(deleted, 1);
        assert_eq!(occupied, 3);
        assert_eq!(empty, 0);

        // Check the order of the remaining items.
        assert_eq!(
            map.iter().collect::<Vec<(&u8, &u8)>>(),
            vec![(&1, &2), (&3, &4), (&4, &5)]
        );

        // Order of the keys must be preserved, but index has been updated.
        assert_eq!(map[0], 2);
        assert_eq!(map[1], 4);
        assert_eq!(map[2], 5);
    }

    #[test]
    fn test_map_remove_nonexistent_key() {
        let mut map = OmniMap::new();

        map.insert(1, 1);

        assert_eq!(map.len(), 1);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 1);

        // Must return None, because the key does not exist.
        assert_eq!(map.remove(&2), None);

        assert_eq!(map.len(), 1);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 1);

        assert_eq!(map.get(&1), Some(&1));
    }

    #[test]
    fn test_map_clear() {
        let mut map = OmniMap::with_capacity(4);

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        assert_eq!(map.len(), 3);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        // Remove an item.
        map.remove(&1);

        assert_eq!(map.len(), 2);
        assert_eq!(map.debug_deleted(), 1);
        assert_eq!(map.capacity(), 4);

        // Clear the map.
        map.clear();

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 4);

        unsafe {
            // All slots must be empty in the index.
            for i in 0..map.capacity() {
                assert_eq!(*map.debug_index_ptr().load(i), Slot::Empty);
            }
        }

        // Reinserting items must work.
        map.insert(1, 2);
        assert_eq!(map.get(&1), Some(&2));
    }

    #[test]
    fn test_map_capacity_reserve() {
        let mut map = OmniMap::new();
        assert_eq!(map.capacity(), 0);

        // Reserve capacity while the map is still unallocated.
        map.reserve(1);

        // Should be fine.
        assert_eq!(map.capacity(), 1);

        map.insert(1, 1);

        // Reserve more capacity in advance.
        map.reserve(10);

        // Capacity must be 1 + requested capacity = 11.
        assert_eq!(map.capacity(), 11);

        // Inserted data are accessible.
        assert_eq!(map.get(&1), Some(&1));
    }

    #[test]
    fn test_map_capacity_shrink_to_fit() {
        let mut map = OmniMap::new();

        assert_eq!(map.capacity(), 0);

        for i in 0..10 {
            map.insert(i, i);
        }

        assert_eq!(map.capacity(), 16);

        // Shrink the capacity to the current length.
        map.shrink_to_fit();

        assert_eq!(map.len(), 10);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 10);

        // All elements are accessible.
        for i in 0..10 {
            assert_eq!(map.get(&i), Some(&i));
        }

        // Remove all elements.
        map.clear();

        // Length must be 0 and capacity must be 10.
        assert_eq!(map.capacity(), 10);
        assert_eq!(map.len(), 0);

        // Shrink the capacity while empty.
        // This should cause deallocation of the internal buffers.
        map.shrink_to_fit();

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 0);
    }

    #[test]
    fn test_map_capacity_shrink_to() {
        let mut map = OmniMap::new();

        assert_eq!(map.capacity(), 0);

        for i in 0..10 {
            map.insert(i, i);
        }

        assert_eq!(map.len(), 10);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 16);

        // Shrink and reserve less than the current length (no effect).
        map.shrink_to(5);

        assert_eq!(map.len(), 10);

        // Capacity must stay 16.
        assert_eq!(map.capacity(), 16);

        // Shrink and reserve greater than the current capacity (no effect).
        map.shrink_to(20);

        assert_eq!(map.len(), 10);

        // Capacity must be adjusted to 16.
        assert_eq!(map.capacity(), 16);

        // Shrink and reserve less than the current capacity and greater than the current length.
        map.shrink_to(12);

        assert_eq!(map.len(), 10);

        // Capacity must be adjusted to 12.
        assert_eq!(map.capacity(), 12);

        // All elements are accessible.
        for i in 0..10 {
            assert_eq!(map.get(&i), Some(&i));
        }

        // Remove all elements.
        map.clear();

        // Length must be 0 and capacity must be 12.
        assert_eq!(map.capacity(), 12);
        assert_eq!(map.len(), 0);

        // Shrink the capacity to 0 while empty.
        // This should cause deallocation of the internal buffers.
        map.shrink_to(0);

        assert_eq!(map.len(), 0);
        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.capacity(), 0);
    }

    #[test]
    fn test_map_iter_empty() {
        let map: OmniMap<u8, u8> = OmniMap::new();

        let mut iter = map.iter();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map_iter_mut_empty() {
        let mut map: OmniMap<u8, u8> = OmniMap::new();

        let mut iter = map.iter_mut();
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map_iter_for_loop() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Immutable borrow.
        for (key, value) in &map {
            assert_eq!(map.get(key), Some(value));
        }
    }

    #[test]
    fn test_map_iter_for_loop_mut() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        // Mutable borrow.
        for (_, value) in &mut map {
            *value += 1;
        }

        for i in 1..4 {
            assert_eq!(map.get(&i), Some(&(i + 2)));
        }
    }

    #[test]
    fn test_map_into_iter_empty() {
        let map: OmniMap<u8, u8> = OmniMap::new();

        let mut iter = map.into_iter();

        // Calling into_iter on an empty map must return an empty iterator.
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map_into_iter() {
        let mut map = OmniMap::new();

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        let mut iter: OmniMapIntoIter<u8, u8> = map.into_iter();

        assert_eq!(iter.next(), Some((1, 2)));
        assert_eq!(iter.next(), Some((2, 3)));
        assert_eq!(iter.next(), Some((3, 4)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map_iter_keys() {
        let mut map = OmniMap::new();

        // Calling iter_keys on an empty map must return an empty iterator.
        assert_eq!(map.iter_keys().next(), None);

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        let keys: Vec<&u8> = map.iter_keys().collect();

        assert_eq!(keys, vec![&1, &2, &3]);
    }

    #[test]
    fn test_map_iter_values() {
        let mut map = OmniMap::new();

        // Calling iter_values on an empty map must return an empty iterator.
        assert_eq!(map.iter_values().next(), None);

        for i in 1..4 {
            map.insert(i, i + 1);
        }

        let values: Vec<&u8> = map.iter_values().collect();

        assert_eq!(values, vec![&2, &3, &4]);
    }

    use std::cell::RefCell;
    use std::rc::Rc;

    #[derive(Debug)]
    struct DropCounter {
        count: Rc<RefCell<usize>>,
    }

    impl Drop for DropCounter {
        fn drop(&mut self) {
            // Increment the drop count.
            *self.count.borrow_mut() += 1;
        }
    }

    #[test]
    fn test_map_into_iter_drop_empty() {
        let map: OmniMap<u8, Box<u8>> = OmniMap::with_capacity(3);

        let mut into_iter = map.into_iter();

        assert!(matches!(into_iter.next(), None));

        // Dropping the iterator should be fine.
        drop(into_iter);
    }

    #[test]
    fn test_map_into_iter_drop() {
        let count = Rc::new(RefCell::new(0));

        let mut map: OmniMap<u8, DropCounter> = OmniMap::new();

        for i in 0..3 {
            map.insert(
                i,
                DropCounter {
                    count: count.clone(),
                },
            );
        }

        let mut into_iter = map.into_iter();

        // The ownership of the value is moved to the stack.
        let moved_value = into_iter.next().unwrap();

        drop(moved_value);

        // The drop count must be 1.
        assert_eq!(*count.borrow(), 1);

        // Dropping the iterator should drop the remaining 2 values only.
        drop(into_iter);

        // The drop count must be 3.
        assert_eq!(*count.borrow(), 3);
    }

    #[test]
    fn test_map_drop_empty() {
        let map: OmniMap<u8, Box<u8>> = OmniMap::with_capacity(3);

        // Dropping the map should be fine.
        drop(map);
    }

    #[test]
    fn test_map_drop() {
        let count = Rc::new(RefCell::new(0));

        let mut map: OmniMap<u8, DropCounter> = OmniMap::new();

        for i in 0..3 {
            map.insert(
                i,
                DropCounter {
                    count: count.clone(),
                },
            );
        }

        // Dropping the map should drop all initialized values.
        drop(map);

        // The drop count must be 3.
        assert_eq!(*count.borrow(), 3);
    }

    #[test]
    fn test_map_clone_empty() {
        let map: OmniMap<u8, &str> = OmniMap::new();

        let cloned = map.clone();

        // Clone must be empty.
        assert_eq!(cloned.len(), 0);
        assert_eq!(cloned.debug_deleted(), 0);
        assert_eq!(cloned.capacity(), 0);
    }

    #[test]
    fn test_map_clone() {
        let mut original = OmniMap::with_capacity(3);

        original.insert(1, 2);
        original.insert(2, 3);

        let mut cloned = original.clone();

        // Clone must have the same length and capacity as the original.
        assert_eq!(cloned.len(), original.len());
        assert_eq!(cloned.debug_deleted(), original.debug_deleted());
        assert_eq!(cloned.capacity(), original.capacity());

        // Entries in the clone must be the same as in the original.
        for (key, value) in original.iter() {
            assert_eq!(cloned.get(key), Some(value));
        }

        // Modifying the clone must not affect the original.
        cloned.insert(3, 4);
        assert_eq!(cloned.len(), original.len() + 1);

        // original length.
        assert_eq!(original.len(), 2);

        // Key in original does not exit.
        assert_eq!(original.get(&3), None);
    }

    #[test]
    fn test_map_clone_compact_empty() {
        let map: OmniMap<u8, &str> = OmniMap::new();

        let cloned = map.clone_compact();

        // Clone must be empty.
        assert_eq!(cloned.len(), 0);
        assert_eq!(cloned.debug_deleted(), 0);
        assert_eq!(cloned.capacity(), 0);
    }

    #[test]
    fn test_map_clone_compact() {
        let mut original = OmniMap::with_capacity(3);

        for i in 1..4 {
            original.insert(i, i + 1);
        }

        // Remove the last item.
        original.pop();

        let mut cloned = original.clone_compact();

        // Clone must have the same length as the original.
        assert_eq!(cloned.len(), original.len());

        // Deleted slots must be removed in the clone.
        assert_ne!(cloned.debug_deleted(), original.debug_deleted());

        // Clone must have a capacity equal to the length of the original.
        assert_eq!(cloned.capacity(), original.len());

        // Entries in the clone must be the same as in the original.
        for (key, value) in original.iter() {
            assert_eq!(cloned.get(key), Some(value));
        }

        // Modifying the clone must not affect the original.
        cloned.insert(3, 4);
        assert_eq!(cloned.len(), original.len() + 1);

        // original length.
        assert_eq!(original.len(), 2);

        // Key in original does not exit.
        assert_eq!(original.get(&3), None);
    }

    #[test]
    fn test_map_partial_eq() {
        let mut map1 = OmniMap::new();
        let mut map2 = OmniMap::new();

        map1.insert(1, "a");
        map1.insert(2, "b");
        map1.insert(3, "c");

        map2.insert(3, "c");
        map2.insert(1, "a");
        map2.insert(2, "b");

        // Must be equal.
        assert_eq!(map1, map2);

        // Modify the second map.
        map2.insert(4, "d");

        // Must not be equal.
        assert_ne!(map1, map2);
    }

    #[test]
    fn test_map_debug() {
        let mut map = OmniMap::with_capacity(3);

        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");

        let debug_str = format!("{:?}", map);
        let expected_str = r#"{1: "a", 2: "b", 3: "c"}"#;

        assert_eq!(debug_str, expected_str);
    }

    #[test]
    fn test_map_index_integrity() {
        let mut map = OmniMap::with_capacity(100);

        // Initial state, all slots must be empty.
        unsafe {
            assert!(map
                .debug_index_ptr()
                .as_slice(map.capacity())
                .iter()
                .all(|slot| matches!(slot, Slot::Empty)));
        }

        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.len(), 0);
        assert_eq!(map.capacity(), 100);

        // Full capacity.
        for i in 0..100 {
            assert_eq!(map.insert(i, i), None);
        }

        // Remove some entries.
        for i in 75..100 {
            assert_eq!(map.remove(&i), Some(i));
        }

        // Collect slots' information.
        let mut occupied_indices = std::collections::HashSet::new();
        let mut empty_indices = 0;
        let mut deleted_indices = 0;

        unsafe {
            for slot in map.debug_index_ptr().as_slice(map.capacity()) {
                match slot {
                    Slot::Occupied(index) => {
                        assert!(
                            occupied_indices.insert(index),
                            "Duplicate index found: {}",
                            index
                        );
                    }
                    Slot::Empty => {
                        empty_indices += 1;
                    }
                    Slot::Deleted => {
                        deleted_indices += 1;
                    }
                }
            }
        }
        // Check integrity.
        assert_eq!(occupied_indices.len(), 75);
        assert_eq!(deleted_indices, 25);
        assert_eq!(
            empty_indices,
            map.capacity() - (occupied_indices.len() + deleted_indices)
        );

        // Compact the map to reindex.
        map.shrink_to_fit();

        // No deleted slots should be present, all slots must be occupied.
        unsafe {
            assert!(map
                .debug_index_ptr()
                .as_slice(map.capacity())
                .iter()
                .all(|slot| matches!(slot, Slot::Occupied(_))));
        }

        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.len(), 75);
        assert_eq!(map.capacity(), 75);

        // Update entries.
        for i in 0..50 {
            map.insert(i, i * 2);
        }

        // Read updated entries.
        for i in 0..50 {
            assert_eq!(map.get(&i), Some(&(i * 2)));
        }

        // Compact the map to reindex.
        map.shrink_to_fit();

        // Remove all entries.
        for i in 0..75 {
            map.remove(&i);
        }

        // No occupied or empty slots should be present, all slots must be deleted.
        unsafe {
            assert!(map
                .debug_index_ptr()
                .as_slice(map.capacity())
                .iter()
                .all(|slot| matches!(slot, Slot::Deleted)));
        }

        assert_eq!(map.debug_deleted(), 75);
        assert_eq!(map.len(), 0);
        assert_eq!(map.capacity(), 75);

        // Insert new entries, the map must be able to reindex successfully.
        for i in 0..100 {
            map.insert(i, i);
        }

        // Map must be reindex successfully, no deleted slots should be present.
        unsafe {
            assert!(map
                .debug_index_ptr()
                .as_slice(map.capacity())
                .iter()
                .all(|slot| !matches!(slot, Slot::Deleted)));
        }

        assert_eq!(map.debug_deleted(), 0);
        assert_eq!(map.len(), 100);
        assert_eq!(map.capacity(), 256);

        // Read updated keys.
        for i in 0..100 {
            assert_eq!(map.get(&i), Some(&i));
        }
    }

    /// These tests check the behavior of the map when the key and value are zero-sized types.
    /// They make sure the behavior is consistent with the behavior of `HashMap` in the
    /// standard library when using zero-sized types.
    #[test]
    fn test_map_zst_keys() {
        // Grow dynamically.
        let mut map = OmniMap::new();

        // Expected op: insert.
        map.insert((), 1);

        // Expected op: update.
        map.insert((), 2);
        map.insert((), 3);

        // Len stays 1.
        assert_eq!(map.len(), 1);

        // Normally it would grow to 4, but capacity will remain invariant after the second insert.
        assert_eq!(map.capacity(), 2);

        // Access the keys returns the last updated value.
        assert_eq!(map.get(&()), Some(&3));

        map.remove(&());

        // Len goes back to 0.
        assert_eq!(map.len(), 0);
        assert_eq!(map.get(&()), None);

        map.shrink_to_fit();

        // Capacity goes back to 0.
        assert_eq!(map.capacity(), 0);
    }

    #[test]
    fn test_map_zst_values() {
        // Grow dynamically.
        let mut map = OmniMap::new();

        // Add 3 items.
        map.insert(1, ());
        map.insert(2, ());
        map.insert(3, ());

        // Len and capacity as usual.
        assert_eq!(map.len(), 3);
        assert_eq!(map.capacity(), 4);

        // Access by get returns &().
        for i in 1..4 {
            assert_eq!(map.get(&i), Some(&()));
        }

        // Access by index returns ().
        for i in 0..3 {
            assert_eq!(map[i], ());
        }

        // Remove an item.
        map.remove(&2);

        assert_eq!(map.len(), 2);
        assert_eq!(map.capacity(), 4);

        map.shrink_to_fit();

        assert_eq!(map.len(), 2);
        assert_eq!(map.capacity(), 2);
    }
}
