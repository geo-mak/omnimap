use core::ops::Range;

use std::alloc::Layout;

use crate::Entry;
use crate::mem::error::{MemoryError, OnError};
use crate::mem::pointers::UnmanagedPointer;

pub(crate) struct Entries<K, V> {
    pointer: UnmanagedPointer<Entry<K, V>>,
}

impl<K, V> Entries<K, V> {
    #[inline(always)]
    pub(crate) const fn new() -> Self {
        Self {
            pointer: UnmanagedPointer::new(),
        }
    }

    /// Creates a new layout for the specified `count` of entries.
    ///
    /// This method checks for **overflow** and valid layout **size** in release-mode, and for
    /// _non-zero_ size in debug-mode.
    ///
    /// **Safety**: count must not be 0.
    #[inline(always)]
    pub(crate) const unsafe fn make_layout(
        &self,
        count: usize,
        on_err: OnError,
    ) -> Result<Layout, MemoryError> {
        unsafe { self.pointer.layout_of(count, on_err) }
    }

    /// Creates a new layout for the specified `count` of entries.
    ///
    /// **Safety**: This method doesn't check for overflow and checks for valid size and alignment
    /// in debug mode only.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn make_layout_unchecked(&self, count: usize) -> Layout {
        unsafe { self.pointer.layout_unchecked_of(count) }
    }

    #[inline]
    pub(crate) fn acquire_memory(
        &mut self,
        layout: Layout,
        on_err: OnError,
    ) -> Result<(), MemoryError> {
        unsafe { self.pointer.acquire(layout, on_err) }
    }

    #[inline]
    pub(crate) fn release_memory(&mut self, layout: Layout) {
        unsafe { self.pointer.release(layout) }
    }

    /// Checks if the pointer is `null`.
    #[must_use]
    #[inline(always)]
    pub(crate) const fn is_null(&self) -> bool {
        self.pointer.is_null()
    }

    /// Returns an instance with copy of the base pointer.
    ///
    /// # Safety
    ///
    /// The returned instance might be `null`.
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn duplicate(&mut self) -> Self {
        unsafe {
            Self {
                pointer: self.pointer.duplicate(),
            }
        }
    }

    /// Returns the base pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ptr(&self) -> *const Entry<K, V> {
        unsafe { self.pointer.as_ptr() }
    }

    /// Returns the base pointer as mutable pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ptr_mut(&self) -> *mut Entry<K, V> {
        unsafe { self.pointer.as_ptr_mut() }
    }

    /// Returns a reference to the element where the current pointer is.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - The value at the current address must be an initialized.
    ///   Accessing an uninitialized entry is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ref(&self) -> &Entry<K, V> {
        unsafe { self.pointer.as_ref() }
    }

    /// Returns a reference to an element at the specified `offset`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - The value at the provided `offset` must be an initialized value of type T.
    ///   Accessing an uninitialized element is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference(&self, offset: usize) -> &Entry<K, V> {
        unsafe { self.pointer.reference(offset) }
    }

    /// Returns a mutable reference to an element at the specified `offset`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - The value at the provided `offset` must be an initialized value of type T.
    ///   Accessing an uninitialized element is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference_mut(&mut self, offset: usize) -> &mut Entry<K, V> {
        unsafe { self.pointer.reference_mut(offset) }
    }

    /// Returns an immutable slice of the initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the slice range `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements is `undefined behavior`.
    #[inline(always)]
    pub(crate) const unsafe fn as_slice(&self, count: usize) -> &[Entry<K, V>] {
        unsafe { self.pointer.as_slice(count) }
    }

    /// Returns a mutable slice over `count` initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the slice range `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Accessing an uninitialized elements is `undefined behavior`.
    #[inline(always)]
    pub(crate) const unsafe fn as_slice_mut(&mut self, count: usize) -> &mut [Entry<K, V>] {
        unsafe { self.pointer.as_slice_mut(count) }
    }

    /// Stores a value at the specified offset `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `offset` must be within the bounds of the allocated memory space.
    ///
    /// - If the offset has already been initialized, the value will be overwritten **without**
    ///   calling `drop`.
    #[inline(always)]
    pub(crate) const unsafe fn store(&mut self, offset: usize, value: Entry<K, V>) {
        unsafe { self.pointer.store(offset, value) }
    }

    /// Reads and returns the value at the specified `offset`.
    ///
    /// This method creates a bitwise copy of `T` with `move` semantics.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `offset` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements is `undefined behavior`.
    ///
    /// - The value at this offset can be in an invalid state after
    ///   calling this method, because it might have been dropped by the caller.
    #[inline(always)]
    pub(crate) const unsafe fn read_for_ownership(&mut self, offset: usize) -> Entry<K, V> {
        unsafe { self.pointer.read_for_ownership(offset) }
    }

    /// Shifts `count` number of values after the provided `offset` to the left,
    /// overwriting the value at that `offset`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `offset + count` must be within the bounds of the allocated memory.
    #[inline(always)]
    pub const unsafe fn shift_left(&mut self, offset: usize, count: usize) {
        unsafe { self.pointer.shift_left(offset, count) }
    }

    /// Copies the value at the offset `src` to the offset `dst`, overwriting the value at `dst`
    /// and leaving the value at `src` unaffected.
    ///
    /// This operation is internally untyped, the initialization state is operationally irrelevant.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `src` and `dst` must be within the bounds of the allocated memory-segment.
    ///
    /// - If the value at offset `dst` has been initialized already, the value will be overwritten **without**
    ///   calling `drop`.
    #[inline(always)]
    pub const unsafe fn memmove_one(&mut self, src: usize, dst: usize) {
        unsafe { self.pointer.memmove_one(src, dst) }
    }

    /// Calls `drop` on the initialized elements with the specified `count` starting from the
    /// offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the drop range `[0, count - 1]`.
    ///
    /// This method is no-op when `count` is `0` or when `T` is of trivial type.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `count` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - Using dropped values after calling this method is `undefined behavior`.
    #[inline(always)]
    pub(crate) unsafe fn drop_initialized(&mut self, count: usize) {
        unsafe { self.pointer.drop_initialized(count) }
    }

    /// Calls `drop` on the initialized elements in the specified range.
    ///
    /// The total drop `count` equals `end - start`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `range` must not be empty.
    ///
    /// - `range` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - Using dropped values after calling this method is `undefined behavior`.
    #[inline(always)]
    pub(crate) unsafe fn drop_range(&mut self, range: Range<usize>) {
        unsafe { self.pointer.drop_range(range) }
    }

    /// Clones values of type `T` from the memory space pointed to by the source pointer `source`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the copy range `[0, count - 1]`.
    ///
    /// This method is unwind-safe. It will call drop on the cloned elements when unwinding
    /// starts.
    ///
    /// This method is no-op if `count` is `0`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment.
    ///
    /// - `clone_count` must be within the bounds of the initialized elements.
    ///   Cloning an uninitialized elements is `undefined behavior`.
    #[inline(always)]
    pub unsafe fn clone_from(&mut self, source: &Entries<K, V>, clone_count: usize)
    where
        K: Clone,
        V: Clone,
    {
        unsafe { self.pointer.clone_from(source.as_ptr(), clone_count) }
    }
}
