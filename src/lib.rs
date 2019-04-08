//! A library that provides a more flexible way to construct
//! and extend the recursive function.
//!
//! The `RecurFn` trait is an abstraction of a recursive function.
//! By accepting a function parameter `recur` as the recursion
//! rather than recurring directly, it makes constructing an
//! anonymous recursive function possible.
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
//! Beside, it makes extending the body of a recursive function possible.
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
//! As `recur_fn` is a convenient way to construct a `RecurFn`,
//! calling it will be slightly slower than direct recursion.
//! To make it zero-cost, consider defining a struct,
//! implementing `RecurFn` trait for it and mark the `body` method by `#[inline]`.
//!
//! ```
//! use recur_fn::RecurFn;
//!
//! let fib = {
//!     struct Fib {}
//!     impl RecurFn<u64, u64> for Fib {
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
//! or if the function doesn't capture anything,
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
//! `DynRecurFn` is a dynamic version of `RecurFn`
//! that allows you to have a trait object.
//!
//! ```
//! use recur_fn::{recur_fn, to_dyn, RecurFn, DynRecurFn};
//! use core::ops::Deref;
//!
//! let dyn_fact: &DynRecurFn<_, _> =
//!     &to_dyn(recur_fn(|fact, n: u64| if n == 0 { 1 } else { n * fact(n - 1) }));
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
/// this trait allows user to customize the recursion.
/// In this way, we can extract and extend the body of a recursive function.
///
/// This trait supports only one argument.
/// If you need multiple arguments, use tuple.
pub trait RecurFn<Arg, Output> {
    /// The body of the recursive function.
    ///
    /// Marking this method by `#[inline]` will make the `call` method
    /// as fast as recurring directly.
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

/// Convert into a `DynRecurFn`
pub fn to_dyn<Arg, Output, R: RecurFn<Arg, Output>>(r: R) -> impl DynRecurFn<Arg, Output> {
    struct DynRecurFnImpl<R>(R);

    impl<Arg, Output, R> DynRecurFn<Arg, Output> for DynRecurFnImpl<R>
    where
        R: RecurFn<Arg, Output>,
    {
        #[inline]
        fn dyn_body(&self, recur: &Fn(Arg) -> Output, arg: Arg) -> Output {
            self.0.body(recur, arg)
        }
    }

    DynRecurFnImpl(r)
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

/// Constructs a `RecurFn` with the body speicified.
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

/// Expands a function definition to defining a struct,
/// implementing `RecurFn` for the struct and constructing it.
/// It can be useful if you want a zero-cost `RecurFn` implementation.
///
/// You can consider it as a function definition,
/// except `fn` keyword is replaced by this macro.
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
mod tests;
