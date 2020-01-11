extern crate std;

use crate::*;
use std::boxed::Box;

#[test]
fn fact_works() {
    let fact = {
        struct Fact {}
        impl RecurFn<i32, i32> for Fact {
            fn body(&self, recur: impl Fn(i32) -> i32, arg: i32) -> i32 {
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
    assert_eq!(90, fact.body(|_| 9, 10));
}

#[test]
fn dyn_works() {
    let fact = recur_fn(|fact, n: i32| if n <= 1 { 1 } else { n * fact(n - 1) });
    let dyn_fact: &dyn DynRecurFn<_, _> = &fact;
    assert_eq!(dyn_fact.call(5), 120);
    let dyn_fact: Box<dyn DynRecurFn<_, _> + Send + Sync> = Box::new(fact);
    assert_eq!(dyn_fact.call(5), 120);
    let from_dyn = from_pointer(dyn_fact);
    assert_eq!(from_dyn.call(5), 120);
}

#[test]
fn lifetime_works() {
    fn test_fact_lifetime(fact_borrow: &dyn DynRecurFn<i32, i32>) {
        let fact = from_pointer(fact_borrow);
        assert_eq!(fact.call(5), 120)
    }
    test_fact_lifetime(&recur_fn(
        |fact, n: i32| if n <= 1 { 1 } else { n * fact(n - 1) },
    ))
}
