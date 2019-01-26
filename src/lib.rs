/// The trait representing a recursive function.
///
/// Instead of recurring directly,
/// this trait uses an injection parameter for recursion,
/// as you can see in `body` method.
///
/// Note that the implementation of this trait may not really recur,
/// i.e. the body method may not call `recur` parameter.
/// In fact, all implementation of `Fn(Arg) -> Output` implements `RecurFn<Arg, Output>`.
///
/// This trait only supports one argument.
/// If you want to have multiple arguments, use tuple.
pub trait RecurFn<Arg, Output> {
    /// The body of the recursive function.
    fn body<F: Fn(Arg) -> Output>
    (&self, recur: F, arg: Arg) -> Output;

    /// Calls the recursive function.
    fn call(&self, arg: Arg) -> Output {
        self.body(|arg| self.call(arg), arg)
    }
}

/// Implement `RecurFn<Arg, Output>` for the normal function `Fn(Arg) -> Output`.
/// The implementation calls the function directly, without calling `recur`.
impl<Arg, Output, F: Fn(Arg) -> Output> RecurFn<Arg, Output> for F {
    fn body<F_: Fn(Arg) -> Output>(&self, _recur: F_, arg: Arg) -> Output {
        self(arg)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn fibonacci_works() {
        let fib = {
            struct Fib {}
            impl RecurFn<usize, usize> for Fib {
                fn body<F: Fn(usize) -> usize>(&self, recur: F, arg: usize) -> usize {
                    if arg <= 2 {
                        1
                    } else {
                        recur(arg - 1) + recur(arg - 2)
                    }
                }
            }
            Fib {}
        };
        for (index, expect) in [1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into_iter().enumerate() {
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
