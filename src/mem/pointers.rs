use core::alloc::Layout;
use core::marker::PhantomData;
use core::ops::Range;
use core::ptr;

use std::alloc::{self, alloc};

#[cfg(debug_assertions)]
use crate::mem::debug::{
    debug_assert_is_null, debug_assert_non_zero_size, debug_assert_not_null,
    debug_assert_valid_alignment, debug_layout_size_align,
};

use crate::mem::error::{MemoryError, OnError};
use crate::opt::OnDrop;
use crate::opt::branch_hints::likely;

/// An indirect reference to _one or more_ values of type `T` consecutively in memory,
/// with set of methods for accessing and managing memory directly.
///
/// It extends the common pointer operations with more operations that simplify the development
/// of custom data structures.
///
/// The simplification factor comes from the fact that it provides a lot of common methods with
/// very rich set of tests related to memory semantics, while at the same it has very simple type
/// requirement `T`. `T` in upper layers can be changed continuously while all tests remain valid.
///
/// It doesn't store any metadata about its allocated memory, such as the size of
/// the allocated memory and the number of initialized elements, therefore it doesn't provide
/// checked operations or automatic memory management.
///
/// Limited checks for invariants are done in debug mode only.
///
/// It uses the registered `#[global_allocator]` to allocate memory.
///
/// Using custom allocators will be supported in the future.
pub(crate) struct UnmanagedPointer<T> {
    ptr: *mut T,
    _t: PhantomData<T>,
}

impl<T> UnmanagedPointer<T> {
    pub(crate) const T_SIZE: usize = size_of::<T>();
    pub(crate) const T_ALIGN: usize = align_of::<T>();
    pub(crate) const MAX_LAYOUT_SIZE: usize = (isize::MAX as usize + 1) - Self::T_ALIGN;

    /// Creates a new pointer set to `null`.
    #[must_use]
    #[inline]
    pub(crate) const fn new() -> Self {
        UnmanagedPointer {
            ptr: ptr::null_mut(),
            _t: PhantomData,
        }
    }

    /// Creates a new layout for the specified `count` of type `T`.
    ///
    /// This method doesn't check for overflow and checks for valid size and alignment in debug
    /// mode only.
    ///
    /// The _resulted size_ must be greater than `0` for whatever reason, this implies that
    /// `T` can't be `ZST`, and the alignment must be power of 2, which implies it can't be zero
    /// also.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn make_layout_unchecked(&self, count: usize) -> Layout {
        unsafe {
            // Checked in debug-mode for overflow as part of Rust's assert_unsafe_precondition.
            let size = count.unchecked_mul(Self::T_SIZE);

            // More constrained size check.
            #[cfg(debug_assertions)]
            debug_layout_size_align(size, Self::T_ALIGN);

            // Also checked in debug-mode by assert_unsafe_precondition.
            Layout::from_size_align_unchecked(size, Self::T_ALIGN)
        }
    }

    /// Creates a new layout for the specified `count` of type `T`.
    ///
    /// This method checks for **overflow** and valid layout **size** in release-mode, and for
    /// _non-zero_ size and valid alignment in debug-mode.
    ///
    /// The _resulted size_ must be greater than `0` for whatever reason, this implies that
    /// `T` can't be `ZST`, and the alignment must be power of 2, which implies it can't be zero
    /// also.
    #[inline(always)]
    pub(crate) const unsafe fn make_layout(
        &self,
        count: usize,
        on_err: OnError,
    ) -> Result<Layout, MemoryError> {
        #[cfg(debug_assertions)]
        debug_assert_valid_alignment(Self::T_ALIGN);

        if let Some(size) = count.checked_mul(Self::T_SIZE) {
            #[cfg(debug_assertions)]
            debug_assert_non_zero_size(size);

            if size > Self::MAX_LAYOUT_SIZE {
                return Err(on_err.layout_err());
            };

            let layout = unsafe { Layout::from_size_align_unchecked(size, Self::T_ALIGN) };
            return Ok(layout);
        }

        Err(on_err.layout_err())
    }

    /// Tries to allocate memory space according to the provided `layout`.
    ///
    /// This method handles allocation error according to the error handling context `on_err`.
    ///
    /// Note that the process may be terminated even if the allocation was successful, because
    /// detecting memory allocation failures at the process-level is platform-specific.
    ///
    /// For instance, on some systems overcommit is allowed by default, which means
    /// that the kernel will map virtual memory to the process regardless of the available memory.
    ///
    /// On such systems, allocation is always reported to be successful, but the process may become a target
    /// for termination later.
    ///
    /// For better safety, consult the platform-specific documentation regarding out-of-memory
    /// (OOM) behavior.
    ///
    /// # Safety
    ///
    /// - Pointer must be `null` before calling this method.
    ///   This method doesn't deallocate the allocated memory space pointed to by this pointer.
    ///   Calling this method with a non-null pointer causes memory leaks, as access to the
    ///   allocated memory space will be lost without freeing it.
    ///
    /// - `align` must be a power of 2.
    ///
    /// - `size` must be greater than `0`, this implies that `T` can't be `ZST`.
    ///
    /// - `size` in bytes, when rounded up to the nearest multiple of `align`, must be less than
    ///   or equal to `isize::MAX` bytes.
    pub(crate) unsafe fn acquire_memory(
        &mut self,
        layout: Layout,
        on_err: OnError,
    ) -> Result<(), MemoryError> {
        #[cfg(debug_assertions)]
        debug_assert_is_null(self.ptr);

        #[cfg(debug_assertions)]
        debug_layout_size_align(layout.size(), layout.align());

        let ptr = unsafe { alloc(layout) as *mut T };

        if likely(!ptr.is_null()) {
            self.ptr = ptr;
            return Ok(());
        }

        Err(on_err.allocator_err(layout))
    }

    /// Releases the memory space pointed to by the pointer according to the provided `layout`.
    ///
    /// This method doesn't call `drop` on the initialized elements.
    ///
    /// The pointer is set to `null` after deallocation.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - Initialized elements will not be dropped before deallocating memory.
    ///   This might cause memory leaks if `T` is not of trivial type, or if the elements are not
    ///   dropped properly before calling this method.
    ///
    /// - `layout` must be the same layout used to allocate the memory space.
    pub(crate) unsafe fn release_memory(&mut self, layout: Layout) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        #[cfg(debug_assertions)]
        debug_layout_size_align(layout.size(), layout.align());

        unsafe { alloc::dealloc(self.ptr as *mut u8, layout) };

        #[cfg(debug_assertions)]
        self.debug_set_pointer_null();
    }

    /// Calls `drop` on the initialized elements with the specified `count` starting from the
    /// offset `0`.
    ///
    /// Indexing is zero-based, the drop range is `[0, count - 1]`.
    ///
    /// This method is no-op when `count` is `0` or when `T` is of trivial type.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `count` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - If `T` is not of trivial type, using dropped values after calling this method is `undefined behavior`.
    #[inline(always)]
    pub(crate) unsafe fn drop_in_place(&mut self, count: usize) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        let drop_slice = ptr::slice_from_raw_parts_mut(self.ptr, count);

        unsafe { drop_slice.drop_in_place() };
    }

    /// Calls `drop` on the initialized elements in the specified range.
    ///
    /// The total drop `count` equals `end - start`.
    ///
    /// This method is no-op if `T` is of a trivial type.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `range` must not be empty.
    ///
    /// - `range` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - If `T` is not of trivial type, using dropped values after calling this method is `undefined behavior`.
    ///
    /// These invariants are checked in debug mode only.
    #[inline(always)]
    pub(crate) unsafe fn drop_range(&mut self, range: Range<usize>) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);
        debug_assert!(!range.is_empty(), "Drop range must not be empty");

        unsafe {
            let drop_ptr = self.ptr.add(range.start);
            let drop_len = range.end - range.start;
            let drop_slice = ptr::slice_from_raw_parts_mut(drop_ptr, drop_len);
            drop_slice.drop_in_place();
        };
    }

    /// Returns an instance with copy of the base pointer.
    ///
    /// # Safety
    ///
    /// The returned instance might be `null`.
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn duplicate(&mut self) -> UnmanagedPointer<T> {
        UnmanagedPointer {
            ptr: self.ptr,
            _t: PhantomData,
        }
    }

    /// Returns the base pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ptr(&self) -> *const T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        self.ptr
    }

    /// Returns the base pointer as mutable pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ptr_mut(&self) -> *mut T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        self.ptr
    }

    /// Returns a reference to the element where the current pointer is.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - The value at the current address must be an initialized value of type T.
    ///   Accessing an uninitialized element as `T` is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn as_ref(&self) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { &*self.ptr }
    }

    /// Returns an immutable slice of the initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, the slice range is `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements as `T` is `undefined behavior`.
    #[inline(always)]
    pub(crate) const unsafe fn as_slice(&self, count: usize) -> &[T] {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        let slice_ptr = ptr::slice_from_raw_parts(self.ptr, count);

        unsafe { &*slice_ptr }
    }

    /// Returns a mutable slice over `count` initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, the slice range is `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Accessing an uninitialized elements as `T` is `undefined behavior`.
    #[inline(always)]
    pub(crate) const unsafe fn as_slice_mut(&mut self, count: usize) -> &mut [T] {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        let slice_ptr = ptr::slice_from_raw_parts_mut(self.ptr, count);

        unsafe { &mut *slice_ptr }
    }

    /// Returns the base pointer as a pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn cast<C>(&self) -> *const C {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        self.ptr.cast::<C>()
    }

    /// Returns the base pointer as a mutable pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn cast_mut<C>(&mut self) -> *mut C {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        self.ptr.cast::<C>()
    }

    /// Increments the pointer's offset by `t_strides` as strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn increment(&mut self, t_strides: usize) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { self.ptr = self.ptr.add(t_strides) };
    }

    /// Decrements the pointer's offset by `t_strides` as strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn decrement(&mut self, t_strides: usize) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { self.ptr = self.ptr.sub(t_strides) };
    }

    /// Writes `0` bytes to `count` values with the size of `T` in the allocated memory space
    /// starting from the offset `0`.
    ///
    /// Indexing is zero-based, the writing range is `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `count` must be within the bounds of the allocated memory space.
    ///
    /// - Initialized elements will be overwritten **without** calling `drop`.
    ///   This might cause memory leaks if `T` is not of trivial type, or if the elements are not
    ///   dropped properly before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn memset_zero(&mut self, count: usize) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { self.ptr.write_bytes(0, count) }
    }

    /// Stores a value at the specified offset `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `offset` must be within the bounds of the allocated memory space.
    ///
    /// - If the offset has already been initialized, the value will be overwritten **without**
    ///   calling `drop`. This might cause memory leaks if the element is not of trivial type,
    ///   or not dropped properly before overwriting.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[inline(always)]
    pub(crate) const unsafe fn store(&mut self, offset: usize, value: T) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { self.ptr.add(offset).write(value) };
    }

    /// Returns a reference to an element at the specified `offset`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - The value at the provided `offset` must be an initialized value of type T.
    ///   Accessing an uninitialized element as `T` is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference(&self, offset: usize) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { &*self.ptr.add(offset) }
    }

    /// Returns a mutable reference to an element at the specified `offset`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - The value at the provided `offset` must be an initialized value of type T.
    ///   Accessing an uninitialized element as `T` is `undefined behavior`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference_mut(&mut self, offset: usize) -> &mut T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { &mut *(self.ptr).add(offset) }
    }

    /// Reads and returns the value at the specified `offset`.
    ///
    /// This method creates a bitwise copy of `T` with `move` semantics.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `offset` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements as `T` is `undefined behavior`.
    ///
    /// - If `T` is not a trivial type, the value at this offset can be in an invalid state after
    ///   calling this method, because it might have been dropped by the caller.
    #[inline(always)]
    pub(crate) const unsafe fn read_for_ownership(&mut self, offset: usize) -> T {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe { self.ptr.add(offset).read() }
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
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe {
            let dst = self.ptr.add(offset);
            let src = dst.add(1);
            dst.copy_from(src, count);
        }
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
    ///   calling `drop`. This might cause memory leaks if the element is not of trivial type,
    ///   or not dropped properly before overwriting.
    #[inline(always)]
    pub const unsafe fn memmove_one(&mut self, src: usize, dst: usize) {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);

        unsafe {
            let src = (self.ptr).add(src);
            let dst = (self.ptr).add(dst);
            dst.copy_from(src, 1);
        }
    }

    /// Clones values of type `T` from the memory space pointed to by the source pointer `source`.
    ///
    /// Indexing is zero-based, the cloning range is `[0, count - 1]`.
    ///
    /// This method is unwind-safe. It will call drop on the cloned elements when unwinding
    /// starts.
    ///
    /// This method is no-op if `count` is `0`.
    ///
    /// # Safety
    ///
    /// - Pointer must point to an already allocated memory-segment aligned to the alignment of `T`.
    ///
    /// - `clone_count` must be within the bounds of the initialized elements.
    ///   Cloning an uninitialized elements as `T` is `undefined behavior`.
    #[inline(always)]
    pub unsafe fn clone_from(&mut self, source: *const T, clone_count: usize)
    where
        T: Clone,
    {
        #[cfg(debug_assertions)]
        debug_assert_not_null(self.ptr);
        debug_assert!(!source.is_null());

        let self_ptr = self.ptr;

        let mut unwind_guard = OnDrop::set_on(0, |cloned| unsafe { self.drop_in_place(*cloned) });

        let i = &mut unwind_guard.arg;

        while *i < clone_count {
            unsafe {
                let src_ptr = source.add(*i);
                let dst_ptr = self_ptr.add(*i);
                dst_ptr.write((*src_ptr).clone());
            }

            *i += 1;
        }

        unwind_guard.set_off();
    }
}

// Debug-mode functions.
#[cfg(debug_assertions)]
impl<T> UnmanagedPointer<T> {
    /// Sets the pointer to null.
    ///
    /// This function is available in debug-mode only.
    const fn debug_set_pointer_null(&mut self) {
        self.ptr = ptr::null_mut();
    }

    /// Checks if the pointer is `null`.
    ///
    /// This function is available in debug-mode only.
    #[must_use]
    pub(crate) const fn debug_is_null(&self) -> bool {
        self.ptr.is_null()
    }
}

#[cfg(test)]
mod alloc_ptr_tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_alloc_ptr_make_layout_unchecked_ok() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout_unchecked(3);
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), UnmanagedPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_alloc_ptr_make_layout_unchecked_zero_size() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout_unchecked(0);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size exceeds maximum limit on this platform")]
    fn test_alloc_ptr_make_layout_unchecked_invalid_size() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout_unchecked(isize::MAX as usize + 1);
        }
    }

    #[test]
    fn test_alloc_ptr_make_layout_ok() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout(3, OnError::Panic).unwrap();
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), UnmanagedPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_alloc_ptr_make_layout_zero_size_panic() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout(0, OnError::Panic);
        }
    }

    #[test]
    #[should_panic(expected = "layout error")]
    fn test_alloc_ptr_make_layout_overflow_panic() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout(usize::MAX, OnError::Panic);
        }
    }

    #[test]
    fn test_alloc_ptr_make_layout_return_err() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let result = alloc_ptr.make_layout(usize::MAX, OnError::ReturnErr);
            assert!(result.is_err());
            assert!(matches!(result, Err(MemoryError::LayoutErr)));
        }
    }

    #[test]
    fn test_alloc_ptr_allocate_deallocate() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();

            let layout = alloc_ptr.make_layout_unchecked(3);

            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            #[cfg(debug_assertions)]
            assert!(!alloc_ptr.debug_is_null());

            alloc_ptr.release_memory(layout);

            #[cfg(debug_assertions)]
            assert!(alloc_ptr.debug_is_null());
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must be null")]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_allocate_allocated() {
        let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout_unchecked(1);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            #[cfg(debug_assertions)]
            assert!(!alloc_ptr.debug_is_null());

            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);
        }
    }

    #[test]
    fn test_alloc_ptr_memset_zero() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            for i in 0..3 {
                assert_ne!(*alloc_ptr.reference(i), 0);
            }

            alloc_ptr.memset_zero(3);

            for i in 0..3 {
                assert_eq!(*alloc_ptr.reference(i), 0);
            }

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_store_access() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            assert_eq!(*alloc_ptr.reference(0), 1);
            assert_eq!(*alloc_ptr.reference(1), 2);
            assert_eq!(*alloc_ptr.reference(2), 3);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_access_mut() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            *alloc_ptr.reference_mut(0) = 10;

            assert_eq!(*alloc_ptr.reference(0), 10);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_access_first() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            assert_eq!(alloc_ptr.as_ref(), &1);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_rfo() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            assert_eq!(alloc_ptr.read_for_ownership(0), 1);

            assert_eq!(*alloc_ptr.reference(1), 2);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_shift_left() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..5 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            alloc_ptr.shift_left(2, 2);

            assert_eq!(*alloc_ptr.reference(0), 1);
            assert_eq!(*alloc_ptr.reference(1), 2);
            assert_eq!(*alloc_ptr.reference(2), 4);
            assert_eq!(*alloc_ptr.reference(3), 5);
            assert_eq!(*alloc_ptr.reference(4), 5);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_move_one() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            alloc_ptr.store(0, 10);
            alloc_ptr.store(1, 20);
            alloc_ptr.store(2, 30);

            alloc_ptr.memmove_one(0, 2);

            assert_eq!(*alloc_ptr.reference(0), 10);
            assert_eq!(*alloc_ptr.reference(1), 20);
            assert_eq!(*alloc_ptr.reference(2), 10);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_alloc_ptr_as_slice_null_ptr() {
        let alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        let slice = unsafe { alloc_ptr.as_slice(0) };
        assert_eq!(slice, &[]);
    }

    #[test]
    fn test_alloc_ptr_as_slice_empty() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            let slice = alloc_ptr.as_slice(0);
            assert_eq!(slice, &[]);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_as_slice() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            let slice = alloc_ptr.as_slice(3);
            assert_eq!(slice, &[1, 2, 3]);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_alloc_ptr_as_slice_mut_null_ptr() {
        let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
        let slice = unsafe { alloc_ptr.as_slice_mut(0) };
        assert_eq!(slice, &mut []);
    }

    #[test]
    fn test_alloc_ptr_as_slice_mut_empty() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            let slice = alloc_ptr.as_slice_mut(0);
            assert_eq!(slice, &[]);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_as_slice_mut() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            let slice = alloc_ptr.as_slice_mut(3);
            assert_eq!(slice, &mut [1, 2, 3]);

            alloc_ptr.release_memory(layout);
        }
    }

    #[derive(Debug)]
    struct DropCounter {
        count: Rc<RefCell<usize>>,
    }

    impl Drop for DropCounter {
        fn drop(&mut self) {
            *self.count.borrow_mut() += 1;
        }
    }

    #[test]
    fn test_alloc_ptr_drop_init() {
        let drop_count = Rc::new(RefCell::new(0));

        unsafe {
            let mut alloc_ptr: UnmanagedPointer<DropCounter> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(
                    i,
                    DropCounter {
                        count: Rc::clone(&drop_count),
                    },
                );
            }

            alloc_ptr.drop_in_place(0);
            assert_eq!(*drop_count.borrow(), 0);

            alloc_ptr.drop_in_place(3);

            assert_eq!(*drop_count.borrow(), 3);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Drop range must not be empty")]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_drop_range_invalid() {
        unsafe {
            let mut alloc_ptr: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);
            alloc_ptr.drop_range(0..0);
        }
    }

    #[test]
    fn test_alloc_ptr_drop_range() {
        let drop_count = Rc::new(RefCell::new(0));

        unsafe {
            let mut alloc_ptr: UnmanagedPointer<DropCounter> = UnmanagedPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.acquire_memory(layout, OnError::Panic);

            for i in 0..5 {
                alloc_ptr.store(
                    i,
                    DropCounter {
                        count: Rc::clone(&drop_count),
                    },
                );
            }

            alloc_ptr.drop_range(0..3);

            assert_eq!(*drop_count.borrow(), 3);

            alloc_ptr.drop_range(3..5);

            alloc_ptr.release_memory(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_clone_from() {
        unsafe {
            let mut source: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let layout = source.make_layout_unchecked(3);
            let _ = source.acquire_memory(layout, OnError::Panic);

            for i in 0..3 {
                source.store(i, i as u8 + 1);
            }

            let mut target: UnmanagedPointer<u8> = UnmanagedPointer::new();
            let _ = target.acquire_memory(layout, OnError::Panic);

            target.clone_from(source.ptr, 3);

            for i in 0..3 {
                assert_eq!(*source.reference(i), *target.reference(i));
            }

            source.release_memory(layout);
            target.release_memory(layout);
        }
    }

    struct PanicOnClone {
        id: usize,
        panic_on: usize,
        dropped: Rc<RefCell<usize>>,
    }

    impl Clone for PanicOnClone {
        fn clone(&self) -> Self {
            if self.id == self.panic_on {
                panic!("A clone with id {} panicked", self.id);
            }
            Self {
                id: self.id,
                panic_on: self.panic_on,
                dropped: Rc::clone(&self.dropped),
            }
        }
    }

    impl Drop for PanicOnClone {
        fn drop(&mut self) {
            *self.dropped.borrow_mut() += 1;
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_clone_from_safe_unwind() {
        let mut source: UnmanagedPointer<PanicOnClone> = UnmanagedPointer::new();
        let mut target: UnmanagedPointer<PanicOnClone> = UnmanagedPointer::new();

        unsafe {
            let layout = source.make_layout_unchecked(10);
            let _ = source.acquire_memory(layout, OnError::Panic);
            let _ = target.acquire_memory(layout, OnError::Panic);

            let drop_counter = Rc::new(RefCell::new(0));

            for i in 0..10 {
                let value = PanicOnClone {
                    id: i,
                    panic_on: 5,
                    dropped: Rc::clone(&drop_counter),
                };
                source.store(i, value);
            }

            let source_ptr = source.cast::<()>();
            let target_ptr = target.cast_mut::<()>();

            let result = std::panic::catch_unwind(move || {
                let mut target = UnmanagedPointer {
                    ptr: target_ptr.cast::<PanicOnClone>(),
                    _t: PhantomData,
                };

                target.clone_from(source_ptr.cast::<PanicOnClone>(), 10);
            });

            assert!(result.is_err());
            assert_eq!(*drop_counter.borrow(), 5);

            source.release_memory(layout);
            target.release_memory(layout);
        }
    }
}
