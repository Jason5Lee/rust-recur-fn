//! A library that provides you a more flexible way to construct
//! and extend the recursive function.
//!
//! The `RecurFn` trait provides a recursive function abstraction
//! that the recursion can be customized.
//!
//! It means that you can construct anonymous recursive function,
//!
//! ```
//! use recur_fn::*;
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
//! use recur_fn::*;
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
//! implement `RecurFn` trait to make it zero-cost.
//!
//! ```
//! use recur_fn::*;
//!
//! let fib = {
//!     struct Fib {}
//!     impl RecurFn<u64, u64> for Fib {
//!         // It's highly recommended to mark `body` method as `#[inline]`,
//!         // otherwise, calling it would be as slow as the one constructed by `recur_fn`,
//!         // which is against the purpose of implementing `RecurFn` manually.
//!         #[inline]
//!         fn body<F: Fn(u64) -> u64>(&self, fib: F, n: u64) -> u64 {
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

/// The recursive function trait.
///
/// Instead of recurring directly,
/// this trait allows user to customize the recursion
/// by accepting `Fn`-type parameter.
/// In this way, we can extract or extend the body of the recursive function.
///
/// This trait only supports one argument.
/// If you need multiple arguments, use tuple.
pub trait RecurFn<Arg, Output> {
    /// The body of the recursive function.
    ///
    /// Performance tip: mark this method `#[inline]` to make the
    /// `call` method as fast as recurring directly.
    fn body<Recur: Fn(Arg) -> Output>
    (&self, recur: Recur, arg: Arg) -> Output;

    /// Call the recursive function.
    #[inline]
    fn call(&self, arg: Arg) -> Output {
        self.body(|arg| self.call(arg), arg)
    }
}

/*
/// The recursive function trait that might mutate the states.
/// It's same as the `RecurFn` trait, except it accept `&mut self` and `FnMut`.
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

/// Implements `RecurFn<Arg, Output>` for `Fn(Arg) -> Output`.
/// It calls the function directly, without calling `recur` parameter.
impl<Arg, Output, F: Fn(Arg) -> Output> RecurFn<Arg, Output> for F {
    fn body<Recur: Fn(Arg) -> Output>(&self, _recur: Recur, arg: Arg) -> Output {
        self(arg)
    }
}

/// Constructs a `RecurFn` by providing a closure as body.
/// This is the most convenient to construct an anonymous `RecurFn`.
///
/// ## Examples
///
/// ```
/// use recur_fn::*;
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
pub fn recur_fn<Arg, Output, F: Fn(&Fn(Arg) -> Output, Arg) -> Output>(body: F) -> impl RecurFn<Arg, Output> {
    struct RecurFnImpl<F>(F);

    impl<Arg, Output, F> RecurFn<Arg, Output> for RecurFnImpl<F>
        where F: Fn(&Fn(Arg) -> Output, Arg) -> Output
    {
        fn body<Recur: Fn(Arg) -> Output>(&self, recur: Recur, arg: Arg) -> Output {
            (self.0)(&recur, arg)
        }

        fn call(&self, arg: Arg) -> Output {
            (self.0)(&|arg| self.call(arg), arg)
        }
    }

    RecurFnImpl(body)
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn fact_works() {
        let fact = {
            struct Fact {}
            impl RecurFn<u64, u64> for Fact {
                fn body<F: Fn(u64) -> u64>(&self, recur: F, arg: u64) -> u64 {
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
    fn fn_works() {
        let mul2 = |n: u64| n * 2;
            assert_eq!(14, RecurFn::call(&mul2, 7));
            assert_eq!(14, mul2.body(
                |_| panic!("Fn implementation should not recur."), 7));
    }
}
