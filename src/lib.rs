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
    fn body<Recur: Fn(Arg) -> Output>
    (&self, recur: Recur, arg: Arg) -> Output;

    /// Calls the recursive function.
    #[inline]
    fn call(&self, arg: Arg) -> Output {
        self.body(|arg| self.call(arg), arg)
    }
}

/// Implements `RecurFn<Arg, Output>` for `Fn(Arg) -> Output`.
/// It calls the function directly, without calling `recur` parameter.
impl<Arg, Output, F: Fn(Arg) -> Output> RecurFn<Arg, Output> for F {
    fn body<Recur: Fn(Arg) -> Output>(&self, _recur: Recur, arg: Arg) -> Output {
        self(arg)
    }
}

/// Constructs a `RecurFn` by a closure.
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
    fn fibonacci_works() {
        let fib = {
            struct Fib {}
            impl RecurFn<usize, usize> for Fib {
                fn body<F: Fn(usize) -> usize>(&self, fib: F, n: usize) -> usize {
                    if n <= 1 {
                        n
                    } else {
                        fib(n - 1) + fib(n - 2)
                    }
                }
            }
            Fib {}
        };
        for (index, expect) in [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into_iter().enumerate() {
            assert_eq!(fib.call(index), *expect);
        }
    }

    #[test]
    fn fact_works() {
        let fact = {
            struct Fact {}
            impl RecurFn<usize, usize> for Fact {
                fn body<F: Fn(usize) -> usize>(&self, recur: F, arg: usize) -> usize {
                    if arg == 0 {
                        1
                    } else {
                        arg * recur(arg - 1)
                    }
                }
            }
            Fact {}
        };
        for (index, expect) in [1, 1, 2, 6, 24, 120, 720, 5040].into_iter().enumerate() {
            assert_eq!(fact.call(index), *expect);
        }
    }

    #[test]
    fn fn_works() {
        let mul2 = |n| n * 2;
        for (index, expect) in [0, 2, 4, 6, 8, 10, 12, 14].into_iter().enumerate() {
            assert_eq!(RecurFn::call(&mul2, index), *expect);
            assert_eq!(mul2.body(
                |_| panic!("Fn should not recur."), index), *expect);
        }
    }
}
