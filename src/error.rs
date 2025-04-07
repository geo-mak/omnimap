use core::alloc::Layout;
use std::alloc::handle_alloc_error;

#[derive(Clone, Copy, Debug)]
pub enum AllocError {
    Overflow,
    AllocatorErr,
}

impl AllocError {
    /// Panics with capacity overflow message.
    #[inline(always)]
    pub(crate) const fn panic_overflow() -> ! {
        panic!("Allocation Error: capacity overflow")
    }
}

#[derive(Clone, Copy)]
pub(crate) enum OnError {
    NoReturn,
    ReturnErr,
}

impl OnError {
    /// Handles `Overflow` error according to the current variant.
    #[must_use]
    #[inline(always)]
    pub(crate) const fn overflow(&self) -> AllocError {
        match self {
            OnError::NoReturn => AllocError::panic_overflow(),
            OnError::ReturnErr => AllocError::Overflow,
        }
    }

    /// Handles `AllocatorErr` according to the current variant.
    #[must_use]
    #[inline(always)]
    pub(crate) fn alloc_err(&self, layout: Layout) -> AllocError {
        match self {
            OnError::NoReturn => handle_alloc_error(layout),
            OnError::ReturnErr => AllocError::AllocatorErr,
        }
    }
}
