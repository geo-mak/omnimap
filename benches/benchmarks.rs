use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

use omnimap::OmniMap;
use std::collections::HashMap;

// Benchmarking module for OmniMap.
// These benchmarks are not exhaustive, and they focus on KPIs like insert, get, remove, etc.
// To run benchmarks, use the following command:
// cargo bench --bench benchmarks

fn bench_insert(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, insert", |b| {
        let mut map = OmniMap::new();
        b.iter(|| {
            for i in 0..10_000 {
                black_box(map.insert(i, i));
            }
        })
    });
}

fn bench_insert_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e4, insert", |b| {
        let mut map = HashMap::new();
        b.iter(|| {
            for i in 0..10_000 {
                black_box(map.insert(i, i));
            }
        })
    });
}

fn bench_get(c: &mut Criterion) {
    let mut map = OmniMap::new();
    for i in 0..10_000 {
        map.insert(i, i);
    }
    c.bench_function("OmniMap, N=1e4, get", |b| {
        b.iter(|| {
            black_box(map.get(&5000));
        })
    });
}

fn bench_get_hashmap(c: &mut Criterion) {
    let mut map = HashMap::new();
    for i in 0..10_000 {
        map.insert(i, i);
    }
    c.bench_function("HashMap, N=1e4, get", |b| {
        b.iter(|| {
            black_box(map.get(&5000));
        })
    });
}

fn bench_first(c: &mut Criterion) {
    let mut map = OmniMap::new();
    for i in 0..10_000 {
        map.insert(i, i);
    }
    c.bench_function("OmniMap, N=1e4, first", |b| {
        b.iter(|| {
            black_box(map.first());
        })
    });
}

fn bench_last(c: &mut Criterion) {
    let mut map = OmniMap::new();
    for i in 0..10_000 {
        map.insert(i, i);
    }
    c.bench_function("OmniMap, N=1e4, last", |b| {
        b.iter(|| {
            black_box(map.last());
        })
    });
}

fn bench_shift_remove(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, shift_remove at N/2", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shift_remove(&5000));
        })
    });
}

fn bench_swap_remove(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, swap_remove at N/2", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.swap_remove(&5000));
        })
    });
}

fn bench_remove_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e4, remove at N/2", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.remove(&5000));
        })
    });
}

fn bench_pop_first(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, pop_front", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.pop_front());
        })
    });
}

fn bench_pop_last(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, pop", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.pop());
        })
    });
}

fn bench_clear(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, clear", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i.to_string());
        }
        b.iter(|| {
            black_box(map.clear());
        })
    });
}

fn bench_clear_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e4, clear", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i.to_string());
        }
        b.iter(|| {
            black_box(map.clear());
        })
    });
}

fn bench_shrink_to(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, shrink_to 11e3", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shrink_to(11_000));
        })
    });
}

fn bench_shrink_to_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e4, shrink_to 11e3", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shrink_to(11_000));
        })
    });
}

fn bench_shrink_to_fit(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, shrink_to_fit", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shrink_to_fit());
        })
    });
}

fn bench_shrink_to_fit_hashmap(c: &mut Criterion) {
    c.bench_function("HashMap, N=1e4, shrink_to_fit", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shrink_to_fit());
        })
    });
}

fn bench_reserve(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, reserve", |b| {
        let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(10_000);
        b.iter(|| {
            black_box(map.reserve(10_000));
        })
    });
}

fn bench_try_reserve(c: &mut Criterion) {
    c.bench_function("OmniMap, N=1e4, try_reserve", |b| {
        let mut map: OmniMap<i32, i32> = OmniMap::with_capacity(10_000);
        b.iter(|| {
            let _ = black_box(map.try_reserve(10_000));
        })
    });
}

fn bench_cmp_eq(c: &mut Criterion) {
    let mut map1 = OmniMap::new();
    for i in 0..10_000 {
        map1.insert(i, i);
    }
    let map2 = map1.clone();
    c.bench_function("OmniMap, N=1e4, cmp eq", |b| {
        b.iter(|| {
            black_box(map1 == map2);
        })
    });
}

fn bench_cmp_eq_hashmap(c: &mut Criterion) {
    let mut map1 = HashMap::new();
    for i in 0..10_000 {
        map1.insert(i, i);
    }
    let map2 = map1.clone();
    c.bench_function("HashMap, N=1e4, cmp eq", |b| {
        b.iter(|| {
            black_box(map1 == map2);
        })
    });
}

criterion_group!(
    benches_insert_get,
    bench_insert,
    bench_insert_hashmap,
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
