#[macro_use]
extern crate criterion;
extern crate recur_fn;

use criterion::Criterion;
use recur_fn::*;

fn fib_direct(n: u64) -> u64 {
    if n < 2 {
        n
    } else {
        fib_direct(n - 1) + fib_direct(n - 2)
    }
}

struct Fib {}

impl RecurFn<u64, u64> for Fib {
    fn body<F: Fn(u64) -> u64>(&self, fib: F, n: u64) -> u64 {
        if n <= 1 {
            n
        } else {
            fib(n - 1) + fib(n - 2)
        }
    }
}

struct FibInline {}

impl RecurFn<u64, u64> for FibInline {
    #[inline]
    fn body<F: Fn(u64) -> u64>(&self, fib: F, n: u64) -> u64 {
        if n <= 1 {
            n
        } else {
            fib(n - 1) + fib(n - 2)
        }
    }
}

fn fib_recur_fn(n: u64) -> u64 {
    recur_fn(|fib, n: u64| {
        if n <= 1 {
            n
        } else {
            fib(n - 1) + fib(n - 2)
        }
    }).call(n)
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib_direct 20", |b| b.iter(|| fib_direct(20)));
    c.bench_function("Fib 20", |b| b.iter(|| Fib {}.call(20)));
    c.bench_function("FibInline 20", |b| b.iter(|| FibInline {}.call(20)));
    c.bench_function("fib_recur_fn 20", |b| b.iter(|| fib_recur_fn(20)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);