## OmniMap
[![CI](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml/badge.svg)](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml)

A key-value data structure with characteristics of both hash maps and vectors.

Originally intended as a lightweight indexed key-value store for high-performance parsers.

## Features
- Relatively simple and compact implementation that mostly relay on `core` intrinsics.
- Maintains the order in which items are inserted.
- Order preservation of items during all operations including: insertion, updating and **removing**.
- Optimized for fast access.

## **Notes**:
- No release has been made yet and must not be considered for production use.
- The public API is not stable and may change in the future.
- Not thread-safe without synchronization primitives.

## Examples

### Create a new OmniMap without initial capacity
```rust
use omnimap::OmniMap;

fn main(){
    // The map will allocate with first insertion and will grow as needed.
    let map: OmniMap<i32, &str> = OmniMap::new();

    assert!(map.is_empty());

    assert_eq!(map.len(), 0);

    assert_eq!(map.capacity(), 0);
}
```

### Create a new OmniMap using the declarative syntax
The declarative syntax consists of a list of key-value pairs separated by a colon `:` and enclosed in curly braces `{}`.
```rust
use omnimap::map;

fn main() {
    // The map will pre-allocate capacity equal to the number of key-value pairs to avoid reallocations.
    let map = map! {
    "one" : 1,
    "two" : 2,
    "three": 3,
    };

    assert_eq!(map.len(), 3);
    assert_eq!(map.capacity(), 3);
    
    // Get the value of key "two".
    assert_eq!(map.get(&"two"), Some(&2));
}
```

### Create a new OmniMap with a capacity
```rust
use omnimap::OmniMap;

fn main(){
    // Creating a map with a capacity is much more efficient when the number of items is known in advance.
    // The map will allocate with the specified capacity and will grow as needed.
    let map: OmniMap<i32, &str> = OmniMap::with_capacity(100);

    assert!(map.is_empty());

    assert_eq!(map.len(), 0);

    assert_eq!(map.capacity(), 100);
}
```

### Create a new OmniMap with capacity using the declarative syntax
```rust
use omnimap::map;

fn main() {
    // The map will allocate with the specified capacity and will grow as needed.
    let map = map! {
    100; // Capacity
    "one" : 1,
    "two" : 2,
    "three": 3,
    };

    assert_eq!(map.len(), 3);
    assert_eq!(map.capacity(), 100);
    
    // Get the value of key "two".
    assert_eq!(map.get(&"two"), Some(&2));
}
```

### Creating new OmniMap with default capacity
```rust
use omnimap::OmniMap;

fn main(){
    // By default, the map will allocate with a capacity of 16.
    let map: OmniMap<i32, &str> = OmniMap::default();

    assert!(map.is_empty());

    assert_eq!(map.len(), 0);

    assert_eq!(map.capacity(), 16);
}
```

### Inserting new items into the map with order preservation
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    // The map now is not empty.
    assert!(!map.is_empty());

    // Length is now 3.
    assert_eq!(map.len(), 3);

    // Order of the items.
    assert_eq!(
        map.iter().collect::<Vec<(&i32, &&str)>>(),
        vec![
            (&1, &"a"),
            (&2, &"b"),
            (&3, &"c")
        ]
    );
}
```

### Updating value of an existing key
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");

    // When updating an existing key, the old value is returned.
    let old_value = map.insert(1, "b");

    assert_eq!(old_value, Some("a"));

    // Value of key `1` has been updated to "b".
    assert_eq!(map.get(&1), Some(&"b"));
}
```

### **Immutable** access to value by key
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");

    // Access value by key immutably.
    assert_eq!(map.get(&1), Some(&"a"));
}
```

### **Mutable** access to value by key
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");

    // Access value by key mutably.
    if let Some(value) = map.get_mut(&1) {
        // Value can be changed.
        *value = "b";
    }

    // Value of key `1` has been changed to "b".
    assert_eq!(map.get(&1), Some(&"b"));
}
```

### Access value by index
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    // Read values by index.
    assert_eq!(map[0], "a");
    assert_eq!(map[1], "b");
    assert_eq!(map[2], "c");

    // Mutate the values by index.
    map[0] = "x";
    map[1] = "y";
    map[2] = "z";

    assert_eq!(map[0], "x");
    assert_eq!(map[1], "y");
    assert_eq!(map[2], "z");
}
```

### **Immutable** access to the first and last items in the map
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    // First item is (1, "a").
    assert_eq!(map.first(), Some((&1, &"a")));

    // Last item is (3, "c").
    assert_eq!(map.last(), Some((&3, &"c")));
}
```

### Removing items and preserve order
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    // Insert 4 items.
    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");
    map.insert(4, "d");

    assert_eq!(map.len(), 4);

    // Remove the second item.
    let removed_value = map.shift_remove(&2);

    // Removed value is "b".
    assert_eq!(removed_value, Some("b"));

    // Length is now 3.
    assert_eq!(map.len(), 3);

    // Key is no longer in the map.
    assert_eq!(map.get(&2), None);

    // The order of the remaining items is preserved.
    assert_eq!(
        map.iter().collect::<Vec<(&i32, &&str)>>(),
        vec![
            (&1, &"a"),
            (&3, &"c"),
            (&4, &"d")
        ]
    );
}
```

### Removing the first item in the map
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    assert_eq!(map.len(), 3);

    // Both, the key and value of the first item are returned.
    let removed_item = map.pop_front();

    // Removed item is (1, "a").
    assert_eq!(removed_item, Some((1, "a")));

    // length is now 2.
    assert_eq!(map.len(), 2);

    // Key is no longer in the map.
    assert_eq!(map.get(&1), None);

    // First key now is the previous second key.
    assert_eq!(map.first(), Some((&2, &"b")));
}
```

### Removing the last item in the map
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    map.insert(1, "a");
    map.insert(2, "b");
    map.insert(3, "c");

    assert_eq!(map.len(), 3);

    // Both, the key and value of the last item are returned.
    let removed_item = map.pop();

    // Removed item is (3, "c").
    assert_eq!(removed_item, Some((3, "c")));

    // length is now 2.
    assert_eq!(map.len(), 2);

    // Key is no longer in the map.
    assert_eq!(map.get(&3), None);

    // Last key now is the second key.
    assert_eq!(map.last(), Some((&2, &"b")));
}
```

### Reserving extra capacity
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::new();

    assert_eq!(map.capacity(), 0);

    map.insert(1, "a");

    assert_eq!(map.capacity(), 1);

    // Reserve capacity in advance.
    map.reserve(10);

    // Capacity must be 11 now.
    assert_eq!(map.capacity(), 11);
}
```

### Shrinking the capacity to fit the number of items
```rust
use omnimap::OmniMap;

fn main(){
    let mut map = OmniMap::default();

    assert_eq!(map.capacity(), 16);

    // Insert 10 items.
    for i in 0..10 {
        map.insert(i, i);
    }

    // By now the capacity is still 16.
    assert_eq!(map.capacity(), 16);

    // Length is 10.
    assert_eq!(map.len(), 10);

    map.shrink_to_fit();

    // Capacity is now equal to the number of items.
    assert_eq!(map.capacity(), 10);
}
```

### Shrinking the map to a specific capacity
```rust
use omnimap::OmniMap;

fn main(){

    let mut map = OmniMap::default();

    assert_eq!(map.capacity(), 16);

    for i in 0..10 {
        map.insert(i, i);
    }

    // By now, the capacity is still 16.
    assert_eq!(map.capacity(), 16);

    // In order to take effect, new capacity must be less than the current capacity and
    // greater than or equal to the number of items in the map.
    map.shrink_to(12);

    // Capacity is now 12.
    assert_eq!(map.capacity(), 12);

    // Shrinking the capacity to a value less than the number of items is no-op.
    map.shrink_to(8);

    // Capacity will not change.
    assert_eq!(map.capacity(), 12);
}
```
