use ::lurk::Lurk;

pub(crate) struct ReduceCount(pub usize);

pub(crate) fn fib(n: usize, reduction_count: ReduceCount) -> Lurk {
    let ReduceCount(reduction_count) = reduction_count;
    Lurk {
        reduction_count,
        input: n,
        name: format!("Lurk: fibonacci-{n} Reduction-{reduction_count}"),
    }
}
