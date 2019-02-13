//! A library that provides you a more flexible way to construct
//! and extend the recursive function.
//!
//! The `RecurFn` trait provides a recursive function abstraction
//! that the recursion can be customized.
//!
//! It means that you can construct anonymous recursive function,
//!
//! ```
//! use recur_fn::{recur_fn, RecurFn};
//!
//! let fib = recur_fn(|fib, n: u64| {
//!     if n <= 1 {
//!         n
//!     } else {
//!         fib(n - 1) + fib(n - 2)
//!     }
//! });
//!
//! assert_eq!(55, fib.call(10));
//! ```
//!
//! and you can extends the body of the recursive function.
//!
//! ```
//! use recur_fn::{recur_fn, RecurFn};
//! use std::cell::RefCell;
//!
//! let fib = recur_fn(|fib, n: u64| {
//!     if n <= 1 {
//!         n
//!     } else {
//!         fib(n - 1) + fib(n - 2)
//!     }
//! });
//!
//! let log = RefCell::new(Vec::new());
//!
//! let fib_with_logging = recur_fn(|recur, n: u64| {
//!     log.borrow_mut().push(n);
//!     fib.body(recur, n)
//! });
//!
//! fib_with_logging.call(3);
//! assert_eq!(*log.borrow(), vec![3, 2, 1, 0, 1]);
//! ```
//!
//! As `recur_fn` is a convenient way to construct `RecurFn`,
//! it comes with cost. You can define a struct and
//! implement `RecurFn` trait to make it zero-cost,
//!
//! ```
//! use recur_fn::RecurFn;
//!
//! let fib = {
//!     struct Fib {}
//!     impl RecurFn<u64, u64> for Fib {
//!         // It's highly recommended to mark `body` method as `#[inline]`,
//!         // otherwise, calling it would not be faster than using `recur_fn`,
//!         // which is against the purpose of implementing `RecurFn` manually.
//!         #[inline]
//!         fn body(&self, fib: impl Fn(u64) -> u64, n: u64) -> u64 {
//!             if n <= 1 {
//!                 n
//!             } else {
//!                 fib(n - 1) + fib(n - 2)
//!             }
//!         }
//!     }
//!     Fib {}
//! };
//!
//! assert_eq!(55, fib.call(10));
//! ```
//!
//! or if the function doesn't need to capture anything,
//! you can use `as_recur_fn` macro.
//!
//! ```
//! use recur_fn::{as_recur_fn, RecurFn};
//!
//! let fact = as_recur_fn!(fact(n: u64) -> u64 {
//!     if n == 0 { 1 } else { n * fact(n - 1) }
//! });
//! assert_eq!(6, fact.call(3));
//! assert_eq!(0,
//!     fact.body(|_| 0, 3));
//! ```
//!
//! `DynRecurFn` is a dynamic version that allows you to have a trait object.
//!
//! ```
//! use recur_fn::{recur_fn, RecurFn, DynRecurFn};
//! use core::ops::Deref;
//!
//! let dyn_fact: &DynRecurFn<_, _> =
//!     &recur_fn(|fact, n: u64| if n == 0 { 1 } else { n * fact(n - 1) });
//
//! assert_eq!(3, dyn_fact.dyn_body(&|_| 1, 3));
//! assert_eq!(3, dyn_fact.body(&|_| 1, 3));
//!
//! // Any type that derefs to `DynRecurFn` implements `RecurFn`.
//! fn test_fact_deref(fact: impl RecurFn<u64, u64>) {
//!     assert_eq!(6, fact.call(3));
//!     assert_eq!(0, fact.body(|_| 0, 3));
//! }
//! test_fact_deref(dyn_fact);
//! ```

#![no_std]
use core::ops::Deref;

/// The recursive function trait.
///
/// Instead of recurring directly,
/// this trait allows user to customize the recursion
/// by accepting `Fn`-type parameter.
/// In this way, we can extract and extend the body of the recursive function.
///
/// This trait only supports one argument.
/// If you need multiple arguments, use tuple.
pub trait RecurFn<Arg, Output> {
    /// The body of the recursive function.
    ///
    /// Performance tip: mark this method `#[inline]` to make the
    /// `call` method as fast as recurring directly.
    fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output;

    /// Calls the recursive function.
    #[inline]
    fn call(&self, arg: Arg) -> Output {
        self.body(|arg| self.call(arg), arg)
    }
}

/// The dynamic version of `RecurFn` that supports trait object.
pub trait DynRecurFn<Arg, Output> {
    /// The body of the recursive function.
    fn dyn_body(&self, recur: &Fn(Arg) -> Output, arg: Arg) -> Output;
}

impl<Arg, Output, R: RecurFn<Arg, Output>> DynRecurFn<Arg, Output> for R {
    fn dyn_body(&self, recur: &Fn(Arg) -> Output, arg: Arg) -> Output {
        self.body(recur, arg)
    }
}

impl<Arg, Output, D: Deref> RecurFn<Arg, Output> for D
where
    D::Target: DynRecurFn<Arg, Output>,
{
    fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output {
        self.deref().dyn_body(&recur, arg)
    }
}

/*
/// The recursive function trait that might mutate the states.
/// It's similar to `RecurFn`, except it accept `&mut self` and `FnMut`.
/// Currently there's a borrow check error that I can't resolve.
pub trait RecurFnMut<Arg, Output> {
    /// The body of the recursive function.
    fn body<Recur: FnMut(Arg) -> Output>
    (&mut self, recur: Recur, arg: Arg) -> Output;

    /// Call the recursive function.
    #[inline]
    fn call(&mut self, arg: Arg) -> Output {
        self.body(|arg| self.call(arg), arg) // Borrow check error here.
    }
}*/

/// Constructs a non-recursive `RecurFn` calling `f` directly.
///
/// # Examples
///
/// ```
/// use recur_fn::{RecurFn, direct};
///
/// let double = direct(|n: u64| n * 2);
/// assert_eq!(4, double.call(2));
/// assert_eq!(20, double.body(|_| 0, 10));
/// ```
pub fn direct<Arg, Output, F: Fn(Arg) -> Output>(f: F) -> impl RecurFn<Arg, Output> {
    struct RecurFnImpl<F>(F);

    impl<Arg, Output, F> RecurFn<Arg, Output> for RecurFnImpl<F>
    where
        F: Fn(Arg) -> Output,
    {
        #[inline]
        fn body(&self, _: impl Fn(Arg) -> Output, arg: Arg) -> Output {
            (self.0)(arg)
        }

        fn call(&self, arg: Arg) -> Output {
            (self.0)(arg)
        }
    }

    RecurFnImpl(f)
}

/// Constructs a `RecurFn` by providing a closure as body.
/// This is the most convenient to construct an anonymous `RecurFn`.
///
/// ## Examples
///
/// ```
/// use recur_fn::{recur_fn, RecurFn};
///
/// let fib = recur_fn(|fib, n: u64| {
///     if n <= 1 {
///         n
///     } else {
///         fib(n - 1) + fib(n - 2)
///     }
/// });
///
/// assert_eq!(55, fib.call(10));
/// ```
pub fn recur_fn<Arg, Output, F>(body: F) -> impl RecurFn<Arg, Output>
where
    F: Fn(&Fn(Arg) -> Output, Arg) -> Output,
{
    struct RecurFnImpl<F>(F);

    impl<Arg, Output, F> RecurFn<Arg, Output> for RecurFnImpl<F>
    where
        F: Fn(&Fn(Arg) -> Output, Arg) -> Output,
    {
        fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output {
            (self.0)(&recur, arg)
        }

        fn call(&self, arg: Arg) -> Output {
            (self.0)(&|arg| self.call(arg), arg)
        }
    }

    RecurFnImpl(body)
}

/// Constructs a zero-cost `RecurFn` implementation that doesn't capture.
///
/// You can consider it as a function definition,
/// except `fn` keyword is replaced by this macro.
///
/// So it's recommended to first write function definition and then
/// change it into this macro, so that the IDE's features can work while
/// you're coding the function's body.
///
/// ## Examples
///
/// ```
/// use recur_fn::{as_recur_fn, RecurFn};
///
/// let fact = as_recur_fn!(fact(n: u64) -> u64 {
///     if n == 0 { 1 } else { n * fact(n - 1) }
/// });
/// assert_eq!(6, fact.call(3));
/// assert_eq!(0,
///     fact.body(|_| 0, 3));
/// ```
#[macro_export]
macro_rules! as_recur_fn {
    ($fn_name:ident ($arg_name:ident: $arg_type:ty) -> $output_type:ty $body:block) => {{
        struct RecurFnImpl {}

        impl RecurFn<$arg_type, $output_type> for RecurFnImpl {
            #[inline]
            fn body(
                &self,
                $fn_name: impl Fn($arg_type) -> $output_type,
                $arg_name: $arg_type,
            ) -> $output_type {
                $body
            }
        }
        RecurFnImpl {}
    }};
}

#[cfg(test)]
mod tests {
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
        let dyn_fib: Box<DynRecurFn<_, _> + Send + Sync> =
            Box::new(recur_fn(
                |fact, n: usize| {
                    if n <= 1 {
                        n
                    } else {
                        n * fact(n - 1)
                    }
                },
            ));

        dyn_fib.call(0);
    }
}
