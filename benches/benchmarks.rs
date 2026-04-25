use core::hint::black_box;
use std::collections::HashMap;

use criterion::{Criterion, criterion_group, criterion_main};

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

/// Linear congruential pseudo-random number generator.
struct RandomNumber {
    seq: usize,
}

impl RandomNumber {
    const MULTIPLIER: usize = 3_787_392_781;

    const fn new() -> Self {
        Self { seq: 0 }
    }
}

impl Iterator for RandomNumber {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.seq = self.seq.wrapping_add(1).wrapping_mul(Self::MULTIPLIER);
        Some(self.seq)
    }
}

fn bench_insert(c: &mut Criterion) {
    let size = 1000;

    c.bench_function("OmniMap, N=1e3, insert", |b| {
        b.iter_with_setup(
            || OmniMap::<usize, usize>::with_capacity(size),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_hashmap(c: &mut Criterion) {
    let size = 1000;

    c.bench_function("HashMap, N=1e3, insert", |b| {
        b.iter_with_setup(
            || HashMap::<usize, usize>::with_capacity(size),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_resize(c: &mut Criterion) {
    let size = 1000;

    c.bench_function("OmniMap, N=1e3, insert resize", |b| {
        b.iter_with_setup(
            || OmniMap::<usize, usize>::new(),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_resize_hashmap(c: &mut Criterion) {
    let size = 1000;

    c.bench_function("HashMap, N=1e3, insert resize", |b| {
        b.iter_with_setup(
            || HashMap::<usize, usize>::new(),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_get(c: &mut Criterion) {
    let size = 1000;

    let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(size);

    for i in (RandomNumber::new()).take(size) {
        map.insert(i, i);
    }

    c.bench_function("OmniMap, N=1e3, get (hit)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).take(size) {
                black_box(map.get(&key));
            }
        })
    });

    c.bench_function("OmniMap, N=1e3, get (miss)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).skip(size).take(size) {
                black_box(map.get(&key));
            }
        })
    });
}

fn bench_get_hashmap(c: &mut Criterion) {
    let size = 1000;

    let mut map: HashMap<usize, usize> = HashMap::with_capacity(size);

    for i in (RandomNumber::new()).take(size) {
        map.insert(i, i);
    }

    c.bench_function("HashMap, N=1e3, get (hit)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).take(size) {
                black_box(map.get(&key));
            }
        })
    });

    c.bench_function("HashMap, N=1e3, get (miss)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).skip(size).take(size) {
                black_box(map.get(&key));
            }
        })
    });
}

fn bench_insert_1e5(c: &mut Criterion) {
    let size = 100_000;

    c.bench_function("OmniMap, N=1e5, insert", |b| {
        b.iter_with_setup(
            || OmniMap::<usize, usize>::with_capacity(size),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_insert_hashmap_1e5(c: &mut Criterion) {
    let size = 100_000;

    c.bench_function("HashMap, N=1e5, insert", |b| {
        b.iter_with_setup(
            || HashMap::<usize, usize>::with_capacity(size),
            |mut map| {
                for i in (RandomNumber::new()).take(size) {
                    black_box(map.insert(i, i));
                }
                map
            },
        );
    });
}

fn bench_get_1e5(c: &mut Criterion) {
    let size = 100_000;

    let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(size);
    for i in (RandomNumber::new()).take(size) {
        map.insert(i, i);
    }

    c.bench_function("OmniMap, N=1e5, get (hit)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).take(size) {
                black_box(map.get(&key));
            }
        })
    });
}

fn bench_get_hashmap_1e5(c: &mut Criterion) {
    let size = 100_000;

    let mut map: HashMap<usize, usize> = HashMap::with_capacity(size);
    for i in (RandomNumber::new()).take(size) {
        map.insert(i, i);
    }

    c.bench_function("HashMap, N=1e5, get (hit)", |b| {
        b.iter(|| {
            for key in (RandomNumber::new()).take(size) {
                black_box(map.get(&key));
            }
        })
    });
}

fn bench_first(c: &mut Criterion) {
    let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(1);
    map.insert(1, 1);
    c.bench_function("OmniMap, N=1, first", |b| {
        b.iter(|| {
            // Absolute constant time.
            black_box(map.first());
        })
    });
}

fn bench_last(c: &mut Criterion) {
    let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(1);
    map.insert(1, 1);
    c.bench_function("OmniMap, N=1, last", |b| {
        b.iter(|| {
            // Absolute constant time.
            black_box(map.last());
        })
    });
}

fn bench_shift_remove(c: &mut Criterion) {
    let size = 100;

    c.bench_function("OmniMap, N=100, shift_remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(size);
                for i in 0..size {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.shift_remove(&50)),
        );
    });
}

fn bench_swap_remove(c: &mut Criterion) {
    let size = 100;

    c.bench_function("OmniMap, N=100, swap_remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(size);
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
    let size = 100;

    c.bench_function("HashMap, N=100, remove at N/2", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<usize, usize> = HashMap::with_capacity(size);
                for i in 0..size {
                    map.insert(i, i);
                }
                map
            },
            |mut map| black_box(map.remove(&50)),
        );
    });
}

fn bench_pop_first(c: &mut Criterion) {
    let size = 100;

    c.bench_function("OmniMap, N=100, pop_front", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(size);
                for i in 0..size {
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
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(1);
                map.insert(1, 1);
                map
            },
            |mut map| black_box(map.pop()),
        );
    });
}

fn bench_clear(c: &mut Criterion) {
    let size = 100;

    c.bench_function("OmniMap, N=100, clear", |b| {
        b.iter_with_setup(
            || {
                let mut map: OmniMap<usize, String> = OmniMap::with_capacity(size);
                for i in 0..size {
                    map.insert(i, i.to_string());
                }
                map
            },
            |mut map| black_box(map.clear()),
        );
    });
}

fn bench_clear_hashmap(c: &mut Criterion) {
    let size = 100;

    c.bench_function("HashMap, N=100, clear", |b| {
        b.iter_with_setup(
            || {
                let mut map: HashMap<usize, String> = HashMap::with_capacity(size);
                for i in 0..size {
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
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(20);
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
                let mut map: HashMap<usize, usize> = HashMap::with_capacity(20);
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
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(20);
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
                let mut map: HashMap<usize, usize> = HashMap::with_capacity(20);
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
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(1);
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
                let mut map: OmniMap<usize, usize> = OmniMap::with_capacity(1);
                map.insert(1, 1);
                map
            },
            |mut map| black_box(map.try_reserve(1)),
        );
    });
}

fn bench_cmp_eq(c: &mut Criterion) {
    let size = 1000;

    let mut map1 = OmniMap::with_capacity(size);

    for i in 0..size {
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
    let size = 1000;

    let mut map1 = HashMap::with_capacity(size);
    for i in 0..size {
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
    bench_insert_1e5,
    bench_insert_hashmap_1e5,
    bench_insert_resize,
    bench_insert_resize_hashmap,
    bench_get,
    bench_get_hashmap,
    bench_get_1e5,
    bench_get_hashmap_1e5,
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
