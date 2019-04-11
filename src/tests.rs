extern crate std;

use crate::*;
use std::boxed::Box;

#[test]
fn fact_works() {
    let fact = {
        struct Fact {}
        impl RecurFn<u64, u64> for Fact {
            fn body(&self, recur: impl Fn(u64) -> u64, arg: u64) -> u64 {
                if arg == 0 {
                    1
                } else {
                    arg * recur(arg - 1)
                }
            }
        }
        Fact {}
    };
    assert_eq!(3628800, fact.call(10));
}

#[test]
fn dyn_works() {
    let fact = recur_fn(|fact, n: usize| if n <= 1 { 1 } else { n * fact(n - 1) });
    let dyn_fact: &DynRecurFn<_, _> = &fact;
    assert_eq!(dyn_fact.call(5), 120);
    assert_eq!(fact.call(5), 120);
    let dyn_fact: Box<DynRecurFn<_, _> + Send + Sync> = Box::new(fact);
    assert_eq!(dyn_fact.call(5), 120);
    let from_dyn = from_pointer(dyn_fact);
    assert_eq!(from_dyn.call(5), 120);
}
