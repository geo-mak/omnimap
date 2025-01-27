/// A builder macro that creates a `OmniMap` from a list of key-value pairs.
///
/// # Examples
///
/// This example creates a `OmniMap` without specifying the capacity.
///
/// > Note: Despite capacity not being specified, the map will be created with a pre-allocated
/// > capacity equal to the number of key-value pairs to avoid resizing.
///
/// ```
/// use omni_map::map;
///
/// let dict = map! {
///  "one" : 1,
///  "two" : 2,
///  "three": 3,
/// };
///
/// assert_eq!(dict.len(), 3);
/// assert_eq!(dict.capacity(), 3);
///
/// assert_eq!(dict.get(&"one"), Some(&1));
/// assert_eq!(dict.get(&"two"), Some(&2));
/// assert_eq!(dict.get(&"three"), Some(&3));
/// ```
///
/// This example creates a `OmniMap` with a specified capacity.
///
/// The capacity is specified before the key-value pairs.
///
/// > Note: The map will pre-allocate according to the `max` of the specified capacity and the
/// > number of key-value pairs to avoid resizing.
///
/// ```
/// use omni_map::map;
///
/// let dict = map! {
///   10; // Capacity
///  "one" : 1,
///  "two" : 2,
///  "three": 3,
/// };
///
/// assert_eq!(dict.len(), 3);
/// assert_eq!(dict.capacity(), 10);
///
/// assert_eq!(dict.get(&"one"), Some(&1));
/// assert_eq!(dict.get(&"two"), Some(&2));
/// assert_eq!(dict.get(&"three"), Some(&3));
/// ```
#[macro_export]
macro_rules! map {
    // Pattern without explicit capacity.
    ( $( $key:tt : $value:expr ),* $(,)? ) => {
        {
            use $crate::OmniMap;

            const KV_COUNT: usize = [$($key),*].len();

            let mut map = OmniMap::with_capacity(KV_COUNT);
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
    // Pattern with explicit capacity.
    ( $capacity:expr; $( $key:tt : $value:expr ),* $(,)? ) => {
        {
            use $crate::OmniMap;

            const KV_COUNT: usize = [$($key),*].len();

            const CAPACITY: usize = if $capacity > KV_COUNT { $capacity } else { KV_COUNT };

            let mut map = OmniMap::with_capacity(CAPACITY);
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
    // Catch-all pattern for invalid patterns.
    ( $($tt:tt)* ) => {
        compile_error!("Invalid syntax. Use `map! { key: value, ... }` or `map! { capacity; key: value, ... }`.");
    };
}

#[cfg(test)]
mod builder_tests {
    #[test]
    fn test_builder_without_capacity() {
        let dict = map! {
            "one" : 1,
            "two" : 2,
            "three": 3,
        };

        assert_eq!(dict.len(), 3);
        assert_eq!(dict.capacity(), 3);

        assert_eq!(dict.get(&"one"), Some(&1));
        assert_eq!(dict.get(&"two"), Some(&2));
        assert_eq!(dict.get(&"three"), Some(&3));
    }

    #[test]
    fn test_builder_with_capacity() {
        let dict = map! {
            10; // Capacity
            "one" : 1,
            "two" : 2,
            "three": 3,
        };

        assert_eq!(dict.len(), 3);
        assert_eq!(dict.capacity(), 10);

        assert_eq!(dict.get(&"one"), Some(&1));
        assert_eq!(dict.get(&"two"), Some(&2));
        assert_eq!(dict.get(&"three"), Some(&3));
    }
}
