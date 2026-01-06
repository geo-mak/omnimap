use core::mem::ManuallyDrop;

/// Compiler hints to prioritize branches over others and improve branch prediction.
pub(crate) mod branch_hints {
    #[cold]
    const fn cold_line() {}

    /// Hints to the compiler that branch `condition` is likely to be true.
    /// Returns the value passed to it.
    #[inline(always)]
    pub(crate) const fn likely(condition: bool) -> bool {
        if condition {
            true
        } else {
            cold_line();
            false
        }
    }

    /// Hints to the compiler that branch `condition` is likely to be false.
    /// Returns the value passed to it.
    #[inline(always)]
    pub(crate) const fn unlikely(condition: bool) -> bool {
        if condition {
            cold_line();
            true
        } else {
            false
        }
    }
}

/// Control structure to execute an expression on drop.
/// Execution can be disabled in the scope using method `finish()`.
pub(crate) struct OnDrop<T, F>
where
    F: FnMut(&mut T),
{
    pub(crate) arg: T,
    on_drop: F,
}

impl<T, F> OnDrop<T, F>
where
    F: FnMut(&mut T),
{
    #[must_use]
    #[inline(always)]
    pub(crate) const fn set(arg: T, on_drop: F) -> OnDrop<T, F> {
        OnDrop { arg, on_drop }
    }

    #[inline(always)]
    pub(crate) const fn finish(self) {
        let _ = ManuallyDrop::new(self);
    }
}

impl<T, F> Drop for OnDrop<T, F>
where
    F: FnMut(&mut T),
{
    #[inline]
    fn drop(&mut self) {
        (self.on_drop)(&mut self.arg)
    }
}
