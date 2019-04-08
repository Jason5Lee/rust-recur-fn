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
fn as_recur_fn_works() {
    let fact = as_recur_fn!(fact(n: u64) -> u64 {
        if n == 0 { 1 } else { n * fact(n - 1) }
    });
    assert_eq!(6, fact.call(3));
    assert_eq!(3, fact.body(|_| 1, 3));
}

#[test]
fn dyn_works() {
    let dyn_fib: Box<DynRecurFn<_, _> + Send + Sync> = Box::new(to_dyn(recur_fn(
        |fact, n: usize| {
            if n <= 1 {
                n
            } else {
                n * fact(n - 1)
            }
        },
    )));

    dyn_fib.call(0);
}

/// A `RecurFn` implementation returns whether `recur` is a dynamic function object.
struct IsDyn;
impl RecurFn<(), bool> for IsDyn {
    fn body(&self, recur: impl Fn(()) -> bool, _: ()) -> bool {
        core::mem::size_of_val(&recur) != 8
    }
}

#[test]
fn test_is_dyn() {
    assert_eq!(core::mem::size_of_val(&|arg| IsDyn {}.call(arg)), 0);
    assert!(!IsDyn {}.call(()));
    assert!(!(&IsDyn {}).call(()));
    assert!((&to_dyn(IsDyn {}) as &DynRecurFn<_, bool>).call(()))
}

#[test]
fn test_issue_1() {
    let box_recur_fn = Box::new(IsDyn {});
    assert!(
        !box_recur_fn.call(()),
        "Calling a `Box` of a concrete `RecurFn` implementation should not go dynamic."
    )
}
