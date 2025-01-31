use criterion::{black_box, criterion_group, criterion_main, Criterion};
use omni_map::OmniMap;
use std::collections::HashMap;

// Benchmarking module for OmniMap.
// These benchmarks are not exhaustive, and they focus on KPIs like insert, get, remove, etc.
// To run benchmarks, use the following command:
// cargo bench --bench benchmarks

fn bench_insert(c: &mut Criterion) {
    let mut map = OmniMap::new();
    c.bench_function("insert 1e4 items", |b| {
        b.iter(|| {
            for i in 0..10_000 {
                black_box(map.insert(i, i));
            }
        })
    });
}

fn bench_insert_hashmap(c: &mut Criterion) {
    let mut map = HashMap::new();
    c.bench_function("insert 1e4 items (std map)", |b| {
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
    c.bench_function("get", |b| {
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
    c.bench_function("get (std map)", |b| {
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
    c.bench_function("get first", |b| {
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
    c.bench_function("get last", |b| {
        b.iter(|| {
            black_box(map.last());
        })
    });
}

fn bench_remove(c: &mut Criterion) {
    c.bench_function("remove", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.remove(&1));
        })
    });
}

fn bench_remove_hashmap(c: &mut Criterion) {
    c.bench_function("remove (std map)", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.remove(&1));
        })
    });
}

fn bench_pop_first(c: &mut Criterion) {
    c.bench_function("pop first", |b| {
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
    c.bench_function("pop", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.pop());
        })
    });
}

fn bench_shrink_to(c: &mut Criterion) {
    // Capacity is 16384, which is 2048 more than HashMap with 10_000 items
    c.bench_function("shrink to 11e3", |b| {
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
    // Capacity is 14336, which 2048 less than OmniMap with 10_000 items
    c.bench_function("shrink to 11e3 (std map)", |b| {
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
    // Capacity is 16384, which is 2048 more than HashMap with 10_000 items
    c.bench_function("shrink to fit", |b| {
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
    // Capacity is 14336, which 2048 less than OmniMap with 10_000 items
    c.bench_function("shrink to fit (std map)", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.shrink_to_fit());
        })
    });
}

fn bench_clear(c: &mut Criterion) {
    c.bench_function("clear 1e4", |b| {
        let mut map = OmniMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.clear());
        })
    });
}

fn bench_clear_hashmap(c: &mut Criterion) {
    c.bench_function("clear 1e4 (std map)", |b| {
        let mut map = HashMap::new();
        for i in 0..10_000 {
            map.insert(i, i);
        }
        b.iter(|| {
            black_box(map.clear());
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
    bench_remove,
    bench_remove_hashmap,
    bench_pop_first,
    bench_pop_last,
    bench_clear,
    bench_clear_hashmap,
);

criterion_group!(
    benches_shrink_ops,
    bench_shrink_to,
    bench_shrink_to_hashmap,
    bench_shrink_to_fit,
    bench_shrink_to_fit_hashmap,
);

criterion_main!(benches_insert_get, benches_remove_ops, benches_shrink_ops);
