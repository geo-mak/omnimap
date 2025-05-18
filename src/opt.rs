use core::mem::ManuallyDrop;

/// Compiler hints to prioritize branches over others and improve branch prediction.
pub(crate) mod branch_prediction {
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

/// A deferred expression that takes effect on drop.
/// Execution can be disabled in the scope using method `deactivate()`.
#[macro_export]
macro_rules! defer {
    ($alias:ident, $body:expr) => {
        $crate::opt::Defer::activate($alias, |$alias| $body)
    };
    ($value:expr, $name:ident, $body:expr) => {
        $crate::opt::Defer::activate($value, |$name| $body)
    };
}

/// Control structure to execute an expression on drop.
/// Execution can be disabled in the scope using method `deactivate()`.
pub(crate) struct Defer<T, F>
where
    F: FnMut(&T),
{
    pub(crate) arg: T,
    on_drop: F,
}

impl<T, F> Defer<T, F>
where
    F: FnMut(&T),
{
    #[must_use]
    #[inline(always)]
    pub(crate) const fn activate(arg: T, on_drop: F) -> Defer<T, F> {
        Defer { arg, on_drop }
    }

    #[inline(always)]
    pub(crate) const fn deactivate(self) {
        let _ = ManuallyDrop::new(self);
    }
}

impl<T, F> Drop for Defer<T, F>
where
    F: FnMut(&T),
{
    #[inline]
    fn drop(&mut self) {
        (self.on_drop)(&self.arg)
    }
}
