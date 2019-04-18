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
//! let fib = recur_fn(|fib, n: i32| {
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
//! let fib = recur_fn(|fib, n: i32| {
//!     if n <= 1 {
//!         n
//!     } else {
//!         fib(n - 1) + fib(n - 2)
//!     }
//! });
//!
//! let log = RefCell::new(Vec::new());
//!
//! let fib_with_logging = recur_fn(|recur, n: i32| {
//!     log.borrow_mut().push(n);
//!     fib.body(recur, n)
//! });
//!
//! fib_with_logging.call(3);
//! assert_eq!(*log.borrow(), vec![3, 2, 1, 0, 1]);
//! ```
//!
//! As `recur_fn` is a convenient way to construct a `RecurFn`,
//! calling it is slower than direct recursion.
//! To make it zero-cost, consider defining a struct,
//! implementing `RecurFn` trait for it and mark the `body` method by `#[inline]`.
//!
//! ```
//! use recur_fn::RecurFn;
//!
//! let fib = {
//!     struct Fib {}
//!     impl RecurFn<i32, i32> for Fib {
//!         #[inline]
//!         fn body(&self, fib: impl Fn(i32) -> i32, n: i32) -> i32 {
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
//! you can use `recur_fn` macro.
//!
//! ```
//! use recur_fn::{recur_fn, RecurFn};
//!
//! let fact = recur_fn!(fact(n: i32) -> i32 {
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
//! use recur_fn::{recur_fn, RecurFn, DynRecurFn};
//! use core::ops::Deref;
//!
//! let dyn_fact: &DynRecurFn<_, _> =
//!     &recur_fn(|fact, n: i32| if n == 0 { 1 } else { n * fact(n - 1) });
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
    fn body(&self, recur: &Fn(Arg) -> Output, arg: Arg) -> Output;
}

impl<Arg, Output, R> DynRecurFn<Arg, Output> for R
where
    R: RecurFn<Arg, Output>,
{
    fn body(&self, recur: &Fn(Arg) -> Output, arg: Arg) -> Output {
        self.body(recur, arg)
    }
}

macro_rules! impl_dyn_with_markers {
    ($($marker:ident),*) => {
        impl<'a, Arg, Output> RecurFn<Arg, Output> for DynRecurFn<Arg, Output> + 'a$( + $marker)*
        {
            fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output {
                self.body(&recur, arg)
            }
        }
    };
}
impl_dyn_with_markers! {}
impl_dyn_with_markers! {Send}
impl_dyn_with_markers! {Sync}
impl_dyn_with_markers! {Send, Sync}

/// A `RecurFn` that delegates to a pointer to a `RecurFn`.
pub struct FromPointer<D>(D);
impl<Arg, Output, D> RecurFn<Arg, Output> for FromPointer<D>
where
    D: Deref,
    D::Target: RecurFn<Arg, Output>,
{
    #[inline]
    fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output {
        self.0.body(recur, arg)
    }
}

/// Returns a `RecurFn` implementation from a pointer
/// to `RecurFn`, i.e. a implementation of `Deref` whose `Target`
/// implements `RecurFn`.
///
/// # Examples
///
/// ```
/// use recur_fn::{RecurFn, recur_fn, from_pointer};
///
/// fn test_fact(fact: impl RecurFn<i32, i32>) {
///     assert_eq!(fact.call(5), 120);
/// }
/// let box_fact = Box::new(recur_fn(
///     |fact, n: i32| {
///         if n <= 1 {
///             1
///         } else {
///             n * fact(n - 1)
///         }
///     },
/// ));
/// test_fact(from_pointer(box_fact));
/// ```
pub fn from_pointer<Arg, Output, D>(d: D) -> FromPointer<D>
where
    D: Deref,
    D::Target: RecurFn<Arg, Output>,
{
    FromPointer(d)
}

/// A `RecurFn` that doesn't call `recur` parameter in its body.
pub struct Direct<F>(F);

impl<Arg, Output, F> RecurFn<Arg, Output> for Direct<F>
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

/// Constructs a non-recursive `RecurFn` calling `f` directly.
///
/// # Examples
///
/// ```
/// use recur_fn::{RecurFn, direct};
///
/// let double = direct(|n: i32| n * 2);
/// assert_eq!(4, double.call(2));
/// assert_eq!(20, double.body(|_| 0, 10));
/// ```
pub fn direct<Arg, Output, F: Fn(Arg) -> Output>(f: F) -> Direct<F> {
    Direct(f)
}

/// A `RecurFn` that uses a closure as the body.
pub struct Closure<F>(F);

impl<Arg, Output, F> RecurFn<Arg, Output> for Closure<F>
where
    F: Fn(&Fn(Arg) -> Output, Arg) -> Output,
{
    fn body(&self, recur: impl Fn(Arg) -> Output, arg: Arg) -> Output {
        self.0(&recur, arg)
    }

    fn call(&self, arg: Arg) -> Output {
        self.0(&|arg| self.call(arg), arg)
    }
}

/// Constructs a `RecurFn` with the body speicified.
///
/// # Examples
///
/// ```
/// use recur_fn::{recur_fn, RecurFn};
///
/// let fib = recur_fn(|fib, n: i32| {
///     if n <= 1 {
///         n
///     } else {
///         fib(n - 1) + fib(n - 2)
///     }
/// });
///
/// assert_eq!(55, fib.call(10));
/// ```
pub fn recur_fn<Arg, Output, F>(body: F) -> Closure<F>
where
    F: Fn(&Fn(Arg) -> Output, Arg) -> Output,
{
    Closure(body)
}

/// Expands a function definition to defining a struct,
/// implementing `RecurFn` for the struct and constructing it.
/// It can be useful if you want a zero-cost `RecurFn` implementation.
///
/// The function should have exactly one argument.
/// `impl Trait`s and generics are not supported.
///
/// # Examples
///
/// ```
/// use recur_fn::{recur_fn, RecurFn};
///
/// let fact = recur_fn!(fact(n: i32) -> i32 {
///     if n == 0 { 1 } else { n * fact(n - 1) }
/// });
/// assert_eq!(6, fact.call(3));
/// assert_eq!(0,
///     fact.body(|_| 0, 3));
/// ```
#[macro_export]
macro_rules! recur_fn {
    ($fn_name:ident ($arg_name:ident: $arg_type:ty) -> $output_type:ty $body:block) => {{
        #[allow(non_camel_case_types)]
        struct $fn_name {}

        impl RecurFn<$arg_type, $output_type> for $fn_name {
            #[inline]
            fn body(
                &self,
                $fn_name: impl Fn($arg_type) -> $output_type,
                $arg_name: $arg_type,
            ) -> $output_type {
                $body
            }
        }
        $fn_name {}
    }};
}

#[cfg(test)]
mod tests;
