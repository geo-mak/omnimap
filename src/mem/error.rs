use core::alloc::Layout;
use std::alloc::handle_alloc_error;

#[derive(Clone, Copy, Debug)]
pub enum AllocError {
    Overflow,
    AllocatorErr,
}

#[derive(Clone, Copy)]
pub(crate) enum OnError {
    Panic,
    ReturnErr,
}

impl OnError {
    /// Handles `Overflow` error according to the current variant.
    #[inline]
    pub(crate) const fn overflow(&self) -> AllocError {
        match self {
            OnError::Panic => panic!("Allocation Error: capacity overflow"),
            OnError::ReturnErr => AllocError::Overflow,
        }
    }

    /// Handles `AllocatorErr` according to the current variant.
    #[inline]
    pub(crate) fn alloc_err(&self, layout: Layout) -> AllocError {
        match self {
            OnError::Panic => handle_alloc_error(layout),
            OnError::ReturnErr => AllocError::AllocatorErr,
        }
    }
}
