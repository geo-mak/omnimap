use core::hint::black_box;
use std::collections::HashMap;

use criterion::{Criterion, criterion_group, criterion_main};
use rand::seq::SliceRandom;

use omnimap::OmniMap;

// Notes:
// These benchmarks are not exhaustive, and they focus on KPIs like insert, get, remove, etc.
//
// Omnimap is a totally different `beast`, so benchmarking in comparison to `std::HashMap`
// is a very, very high bar because:
// - Omnimap allocates and manages two memory segments, one for entries, and one for the index.
// - Omnimap doesn't utilize SIMD instruction and relies solely on normal compiler optimizations.
// - Omnimap's current capacity management is not especially optimized.
//
// To run benchmarks, use the following command:
// cargo bench --bench benchmarks

fn bench_insert(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e3, insert", |b| {
        b.iter_with_setup(
            || OmniMap::<i32, i32>::with_capacity(1000),
            |mut map| {
                for i in 0..1000 {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e3, insert", |b| {
        b.iter_with_setup(
            || HashMap::<i32, i32>::with_capacity(1000),
            |mut map| {
                for i in 0..1000 {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_resize(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e3, insert resize", |b| {
        b.iter_with_setup(
            || OmniMap::<i32, i32>::new(),
            |mut map| {
                for i in 0..1000 {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_resize_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e3, insert resize", |b| {
        b.iter_with_setup(
            || HashMap::<i32, i32>::new(),
            |mut map| {
                for i in 0..1000 {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_get(c: &mut Criterion) {
    let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1000);

    for i in 0..1000 {
        map.insert(i, i);
    }

    let mut rng_state = rand::rng();
    let mut keys: Vec<i32> = (0..1000).collect();
    keys.shuffle(&mut rng_state);

    c.bench_function("OmniMap, N=1e3, get", |b| {
        let mut key_idx = 0;
        b.iter(|| {
            let key = keys[key_idx];
            black_box(map.get(&key));
            key_idx = (key_idx + 1) % 1000;
        })
    });
}

fn bench_get_hashmap(c: &mut Criterion) {
    let mut map: HashMap<i32, i32> = HashMap::with_capacity(1000);
    for i in 0..1000 {
        map.insert(i, i);
    }

    let mut rng_state = rand::rng();
    let mut keys: Vec<i32> = (0..1000).collect();
    keys.shuffle(&mut rng_state);

    c.bench_function("HashMap, N=1e3, get", |b| {
        let mut key_idx = 0;
        b.iter(|| {
            let key = keys[key_idx];
            black_box(map.get(&key));
            key_idx = (key_idx + 1) % 1000;
        })
    });
}

fn bench_first(c: &mut Criterion) {
    let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1);
    map.insert(1, 1);
    c.bench_function("OmniMap, N=1, first", |b| {
        b.iter(|| {
            black_box(map.first());
        })
    });
}

fn bench_last(c: &mut Criterion) {
    let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1);
    map.insert(1, 1);
    c.bench_function("OmniMap, N=1, last", |b| {
        b.iter(|| {
            black_box(map.last());
        })
    });
}

fn bench_shift_remove(c: &mut Criterion) {
    c.bench_function("OmniMap, N=100, shift_remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shift_remove(&50)),
        );
    });
}

fn bench_swap_remove(c: &mut Criterion) {
    c.bench_function("OmniMap, N=100, swap_remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.swap_remove(&50)),
        );
    });
}

fn bench_remove_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=100, remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.remove(&50)),
        );
    });
}

fn bench_pop_first(c: &mut Criterion) {
    c.bench_function("OmniMap, N=100, pop_front", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.pop_front()),
        );
    });
}

fn bench_pop_last(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1, pop", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1);
                map.insert(1, 1);
                map
            },
            |mut map| black_box(map.pop()),
        );
    });
}

fn bench_clear(c: &mut Criterion) {
    c.bench_function("OmniMap, N=100, clear", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, String> = OmniMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i.to_string());
                }
                map
            },
            |mut map| black_box(map.clear()),
        );
    });
}

fn bench_clear_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=100, clear", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<i32, String> = HashMap::with_capacity(100);
                for i in 0..100 {
                    map.insert(i, i.to_string());
                }
                map
            },
            |mut map| black_box(map.clear()),
        );
    });
}

fn bench_shrink_to(c: &mut Criterion) {
    c.bench_function("OmniMap, N=20, shrink_to 0", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(20);
                for i in 0..10 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shrink_to(0)),
        );
    });
}

fn bench_shrink_to_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=20, shrink_to 0", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<i32, i32> = HashMap::with_capacity(20);
                for i in 0..10 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shrink_to(0)),
        );
    });
}

fn bench_shrink_to_fit(c: &mut Criterion) {
    c.bench_function("OmniMap, N=20, shrink_to_fit", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(20);
                for i in 0..10 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shrink_to_fit()),
        );
    });
}

fn bench_shrink_to_fit_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=20, shrink_to_fit", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<i32, i32> = HashMap::with_capacity(20);
                for i in 0..10 {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shrink_to_fit()),
        );
    });
}

fn bench_reserve(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1, reserve", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1);
                map.insert(1, 1);
                map
            },
            |mut map| black_box(map.reserve(1)),
        );
    });
}

fn bench_try_reserve(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1, try_reserve", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(1);
                map.insert(1, 1);
                map
            },
            |mut map| black_box(map.try_reserve(1)),
        );
    });
}

fn bench_cmp_eq(c: &mut Criterion) {
    let mut map1 = OmniMap::with_capacity(1000);
    for i in 0..1000 {
        map1.insert(i, i);
    }
    let map2 = map1.clone();
    c.bench_function("OmniMap, N=1e3, cmp eq", |b| {
        b.iter(|| {
            black_box(map1 == map2);
        })
    });
}

fn bench_cmp_eq_hashmap(c: &mut Criterion) {
    let mut map1 = HashMap::with_capacity(1000);
    for i in 0..1000 {
        map1.insert(i, i);
    }
    let map2 = map1.clone();
    c.bench_function("HashMap, N=1e3, cmp eq", |b| {
        b.iter(|| {
            black_box(map1 == map2);
        })
    });
}

criterion_group!(
    benches_insert_get,
    bench_insert,
    bench_insert_hashmap,
    bench_insert_resize,
    bench_insert_resize_hashmap,
    bench_get,
    bench_get_hashmap,
    bench_first,
    bench_last,
);

criterion_group!(
    benches_remove_ops,
    bench_shift_remove,
    bench_swap_remove,
    bench_remove_hashmap,
    bench_pop_first,
    bench_pop_last,
    bench_clear,
    bench_clear_hashmap,
);

criterion_group!(
    benches_shrink_reserve_ops,
    bench_shrink_to,
    bench_shrink_to_hashmap,
    bench_shrink_to_fit,
    bench_shrink_to_fit_hashmap,
    bench_reserve,
    bench_try_reserve,
);

criterion_group!(benches_comparison, bench_cmp_eq, bench_cmp_eq_hashmap,);

criterion_main!(
    benches_insert_get,
    benches_remove_ops,
    benches_shrink_reserve_ops,
    benches_comparison
);
