/// Branching optimizer with collection of compiler hints to prioritize branches over others
/// and improve branch prediction.
pub(crate) struct BranchOptimizer;

impl BranchOptimizer {
    #[cold]
    const fn cold_line() {}

    /// Hints to the compiler that branch `condition` is likely to be true.
    /// Returns the value passed to it.
    ///
    /// Any use other than with `if` statements will probably not have an effect.
    #[inline(always)]
    pub(crate) const fn likely(condition: bool) -> bool {
        if condition {
            true
        } else {
            Self::cold_line();
            false
        }
    }

    /// Hints to the compiler that branch `condition` is likely to be false.
    /// Returns the value passed to it.
    ///
    /// Any use other than with `if` statements will probably not have an effect.
    #[inline(always)]
    pub(crate) const fn unlikely(condition: bool) -> bool {
        if condition {
            Self::cold_line();
            true
        } else {
            false
        }
    }
}
