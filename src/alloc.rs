use core::alloc::Layout;
use core::marker::PhantomData;
use core::ops::Range;
use core::ptr;

use std::alloc::{self, alloc};

use crate::error::{AllocError, OnError};
use crate::opt::OnDrop;
use crate::opt::branch_hints::likely;

/// Debug-mode check for the valid alignment.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - `align` of `T` must not be zero.
///
/// - `align` of `T` must be a power of two.
#[cfg(debug_assertions)]
const fn debug_assert_valid_alignment(align: usize) {
    assert!(align.is_power_of_two(), "Alignment must be a power of two");
}

/// Debug-mode check for the valid allocation size.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - `size` must be greater than `0`.
#[cfg(debug_assertions)]
const fn debug_assert_non_zero_size(size: usize) {
    assert!(size > 0, "Allocation size must be greater than 0");
}

/// Debug-mode check for the layout size and alignment.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - `align` of `T` must not be zero.
///
/// - `align` of `T` must be a power of two.
///
/// - `size` must be greater than `0`.
///
/// - `size`, when rounded up to the nearest multiple of `align`, must be less than or
///   equal to `isize::MAX`.
///
#[cfg(debug_assertions)]
const fn debug_layout_size_align(size: usize, align: usize) {
    debug_assert_valid_alignment(align);
    debug_assert_non_zero_size(size);
    assert!(
        (isize::MAX as usize + 1) - align > size,
        "Allocation size exceeds maximum limit on this platform"
    );
}

/// Debug-mode check to check the allocation state.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - The pointer must not be null.
///
#[cfg(debug_assertions)]
const fn debug_assert_allocated<T>(instance: &AllocationPointer<T>) {
    assert!(!instance.ptr.is_null(), "Pointer must not be null");
}

/// Debug-mode check to check the allocation state.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - The pointer must be null.
///
#[cfg(debug_assertions)]
const fn debug_assert_not_allocated<T>(instance: &AllocationPointer<T>) {
    assert!(instance.ptr.is_null(), "Pointer must be null");
}

/// An indirect reference to _one or more_ values of type `T` consecutively in memory,
/// with methods for managing the underlying memory directly.
///
/// It guarantees proper `size` and `alignment` of `T`, when storing or accessing
/// values, but it doesn't guarantee safe operations with measures such as null pointer checks or
/// bounds checking.
///
/// Moreover, it doesn't store any metadata about its allocated memory, such as the size of
/// the allocated memory and the number of initialized elements, therefore it doesn't offer
/// automatic memory management.
///
/// If `T` is not of trivial type, `drop` must be called on the elements to release resources
/// before deallocating the allocated memory.
///
/// Limited checks for invariants are done in debug mode only.
///
/// It uses the registered `#[global_allocator]` to allocate memory.
///
/// Using custom allocators will be supported in the future.
pub(crate) struct AllocationPointer<T> {
    ptr: *mut T,
    _marker: PhantomData<T>,
}

impl<T> AllocationPointer<T> {
    pub(crate) const T_SIZE: usize = size_of::<T>();
    pub(crate) const T_ALIGN: usize = align_of::<T>();
    pub(crate) const T_MAX_ALLOC_SIZE: usize = (isize::MAX as usize + 1) - Self::T_ALIGN;

    /// Creates a new `MemorySpace` without allocating memory.
    ///
    /// The pointer is set to `null`.
    ///
    #[must_use]
    #[inline]
    pub(crate) const fn new() -> Self {
        AllocationPointer {
            ptr: ptr::null_mut(),
            _marker: PhantomData,
        }
    }

    /// Checks if the pointer of `MemorySpace` is null.
    #[must_use]
    #[inline(always)]
    pub(crate) const fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    /// Returns an instance with copy of the base pointer.
    ///
    /// # Safety
    ///
    /// This method doesn't provide any guarantees about the state of the returned pointer and its
    /// allocated memory space.
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn duplicate(&mut self) -> AllocationPointer<T> {
        AllocationPointer {
            ptr: self.ptr,
            _marker: PhantomData,
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
    ) -> Result<Layout, AllocError> {
        #[cfg(debug_assertions)]
        debug_assert_valid_alignment(Self::T_ALIGN);

        if let Some(size) = count.checked_mul(Self::T_SIZE) {
            #[cfg(debug_assertions)]
            debug_assert_non_zero_size(size);

            if Self::T_MAX_ALLOC_SIZE > size {
                let layout = unsafe { Layout::from_size_align_unchecked(size, Self::T_ALIGN) };
                return Ok(layout);
            }
        }

        Err(on_err.overflow())
    }

    /// Allocates memory space according to the provided `layout`.
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
    ///
    /// # Returns
    ///
    /// `Ok(())`: If the allocation was successful.
    /// `Err(AllocError)`: If the allocation was unsuccessful.
    pub(crate) unsafe fn allocate(
        &mut self,
        layout: Layout,
        on_err: OnError,
    ) -> Result<(), AllocError> {
        #[cfg(debug_assertions)]
        debug_assert_not_allocated(self);

        #[cfg(debug_assertions)]
        debug_layout_size_align(layout.size(), layout.align());

        let ptr = unsafe { alloc(layout) as *mut T };

        if likely(!ptr.is_null()) {
            self.ptr = ptr;
            return Ok(());
        }

        Err(on_err.alloc_err(layout))
    }

    /// Deallocates the memory space pointed to by the pointer according to the provided `layout`.
    ///
    /// This method doesn't call `drop` on the initialized elements.
    ///
    /// The pointer is set to `null` after deallocation.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - Initialized elements will not be dropped before deallocating memory.
    ///   This might cause memory leaks if `T` is not of trivial type, or if the elements are not
    ///   dropped properly before calling this method.
    ///
    /// - `layout` must be the same layout used to allocate the memory space.
    pub(crate) unsafe fn deallocate(&mut self, layout: Layout) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        #[cfg(debug_assertions)]
        debug_layout_size_align(layout.size(), layout.align());

        unsafe { alloc::dealloc(self.ptr as *mut u8, layout) };

        self.ptr = ptr::null_mut();
    }

    /// Returns the base pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn ptr(&self) -> *const T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr
    }

    /// Returns the base pointer as mutable pointer.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn ptr_mut(&self) -> *mut T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr
    }

    /// Returns the base pointer as a pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn base_as<C>(&self) -> *const C {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr as *const C
    }

    /// Returns the base pointer as a mutable pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn base_mut_as<C>(&mut self) -> *mut C {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr as *mut C
    }

    /// Sets the base pointer at current offset plus `t_offset` of the strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn set_plus(&mut self, t_offset: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { self.ptr = self.ptr.add(t_offset) };
    }

    /// Sets the base pointer at current offset minus `t_offset` of the strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn set_minus(&mut self, t_offset: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { self.ptr = self.ptr.sub(t_offset) };
    }

    /// Writes `0` bytes to `count` values with the size of `T` in the allocated memory space
    /// starting from the offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the writing range `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `count` must be within the bounds of the allocated memory space.
    ///
    /// - Initialized elements will be overwritten **without** calling `drop`.
    ///   This might cause memory leaks if `T` is not of trivial type, or if the elements are not
    ///   dropped properly before calling this method.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) where `n` is the `count` of type `T`.
    #[inline(always)]
    pub(crate) const unsafe fn memset_zero(&mut self, count: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { ptr::write_bytes(self.ptr, 0, count) };
    }

    /// Stores a value at the specified offset `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `at` must be within the bounds of the allocated memory space.
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
    pub(crate) const unsafe fn store(&mut self, at: usize, value: T) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { ptr::write((self.ptr).add(at), value) };
    }

    /// Returns a reference to an element at the specified offset `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGSEGV`.
    ///
    /// - The value of type `T` at the offset `at` must be initialized. Accessing an uninitialized
    ///   element as `T` is `undefined behavior`.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference(&self, at: usize) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { &*self.ptr.add(at) }
    }

    /// Returns a mutable reference to an element at the specified offset `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGSEGV`.
    ///
    /// - The value of type `T` at the offset `at` must be initialized. Accessing an uninitialized
    ///   element as `T` is `undefined behavior`.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference_mut(&mut self, at: usize) -> &mut T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { &mut *(self.ptr).add(at) }
    }

    /// Returns a reference to the first element.
    ///
    /// # Safety
    ///
    /// This method checks for out of bounds access in debug mode only.
    ///
    /// The caller must ensure that the `MemorySpace` is not empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn reference_first(&self) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { &*self.ptr }
    }

    /// Reads and returns the value at the specified offset `at`.
    ///
    /// This method creates a bitwise copy of `T` with `move` semantics.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null ptr will cause termination with `SIGABRT`.
    ///
    /// - `at` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements as `T` is `undefined behavior`.
    ///
    /// - If `T` is not a trivial type, the value at this offset can be in an invalid state after
    ///   calling this method, because it might have been dropped by the caller.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    #[inline(always)]
    pub(crate) const unsafe fn read_for_ownership(&mut self, at: usize) -> T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { ptr::read((self.ptr).add(at)) }
    }

    /// Shifts the `count` values after `at` to the left, overwriting the value at `at`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null ptr will cause termination with `SIGABRT`.
    ///
    /// - `at + count` must be within the bounds of the allocated memory space.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) where `n` is the number (`count`) of the elements to be shifted.
    #[inline(always)]
    pub const unsafe fn shift_left(&mut self, at: usize, count: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe {
            let dst = (self.ptr).add(at);
            let src = dst.add(1);
            ptr::copy(src, dst, count);
        }
    }

    /// Copies the value at the offset `from` to the offset `to`, overwriting the value at `to`
    /// and leaving the value at `from` unaffected.
    ///
    /// This operation is internally untyped, the initialization state is operationally irrelevant.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null ptr will cause termination with `SIGABRT`.
    ///
    /// - `from` and `to` must be within the bounds of the allocated memory space.
    ///
    /// - If the offset `to` has already been initialized, the value will be overwritten **without**
    ///   calling `drop`. This might cause memory leaks if the element is not of trivial type,
    ///   or not dropped properly before overwriting.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    #[inline(always)]
    pub const unsafe fn memmove_one(&mut self, from: usize, to: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe {
            let src = (self.ptr).add(from);
            let dst = (self.ptr).add(to);
            ptr::copy(src, dst, 1);
        }
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
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `count` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - If `T` is not of trivial type, using dropped values after calling this method can cause
    ///   `undefined behavior`.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) where `n` is the number (`count`) of the elements to be dropped.
    ///
    #[inline(always)]
    pub(crate) unsafe fn drop_initialized(&mut self, count: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr, count)) };
    }

    /// Calls `drop` on the initialized elements in the specified range.
    ///
    /// The total drop `count` equals `end - start - 1`.
    ///
    /// This method is no-op if `T` is of a trivial type.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `range` must not be empty.
    ///
    /// - `range` must be within the bounds of the **initialized** elements.
    ///   Calling `drop` on uninitialized elements is `undefined behavior`.
    ///
    /// - If `T` is not of trivial type, using dropped values after calling this method is
    ///   `undefined behavior`.
    ///
    /// These invariants are checked in debug mode only.
    ///
    /// # Time Complexity
    ///
    /// _O_(n) where `n` is the number (`count`) of the elements to be dropped.
    ///
    #[inline(always)]
    pub(crate) unsafe fn drop_range(&mut self, range: Range<usize>) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);
        debug_assert!(!range.is_empty(), "Drop range must not be empty");

        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.ptr.add(range.start),
                range.end - range.start,
            ))
        };
    }

    /// Returns an immutable slice of the initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the slice range `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Loading an uninitialized elements as `T` is `undefined behavior`.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[inline(always)]
    pub(crate) const unsafe fn as_slice(&self, count: usize) -> &[T] {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { &*ptr::slice_from_raw_parts(self.ptr, count) }
    }

    /// Returns a mutable slice over `count` initialized elements starting from the offset `0`.
    ///
    /// Indexing is zero-based, i.e., the last element is at offset `count - 1`, this will make
    /// the slice range `[0, count - 1]`.
    ///
    /// # Safety
    ///
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `count` must be within the bounds of the initialized elements.
    ///   Accessing an uninitialized elements as `T` is `undefined behavior`.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[inline(always)]
    pub(crate) const unsafe fn as_slice_mut(&mut self, count: usize) -> &mut [T] {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        unsafe { &mut *ptr::slice_from_raw_parts_mut(self.ptr, count) }
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
    /// - Pointer must be allocated before calling this method.
    ///   Calling this method with a null pointer will cause termination with `SIGABRT`.
    ///
    /// - `clone_count` must be within the bounds of the initialized elements.
    ///   Cloning an uninitialized elements as `T` is `undefined behavior`.
    #[inline(always)]
    pub(crate) unsafe fn clone_from(&mut self, source: *const T, clone_count: usize)
    where
        T: Clone,
    {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);
        debug_assert!(!source.is_null());

        let self_ptr = self.ptr;

        let cloned = 0;

        let mut drop_guard =
            OnDrop::set(cloned, |cloned| unsafe { self.drop_initialized(*cloned) });

        unsafe {
            for i in 0..clone_count {
                let src = source.add(i);
                let dst = self_ptr.add(i);
                ptr::write(dst, (*src).clone());
                drop_guard.arg += 1;
            }
        }

        // Cloned successfully (If any).
        drop_guard.finish();
    }
}

#[cfg(test)]
mod alloc_ptr_tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_alloc_ptr_new() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        assert!(alloc_ptr.is_null());
    }

    #[test]
    fn test_alloc_ptr_make_layout_unchecked_ok() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout_unchecked(3);
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), AllocationPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_alloc_ptr_make_layout_unchecked_zero_size() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout_unchecked(0);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size exceeds maximum limit on this platform")]
    fn test_alloc_ptr_make_layout_unchecked_invalid_size() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout_unchecked(isize::MAX as usize);
        }
    }

    #[test]
    fn test_alloc_ptr_make_layout_ok() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout(3, OnError::Panic).unwrap();
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), AllocationPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_alloc_ptr_make_layout_zero_size_panic() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout(0, OnError::Panic);
        }
    }

    #[test]
    #[should_panic(expected = "Allocation Error: capacity overflow")]
    fn test_alloc_ptr_make_layout_overflow_panic() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let _ = alloc_ptr.make_layout(usize::MAX, OnError::Panic);
        }
    }

    #[test]
    fn test_alloc_ptr_make_layout_return_err() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let result = alloc_ptr.make_layout(usize::MAX, OnError::ReturnErr);
            assert!(result.is_err());
            assert!(matches!(result, Err(AllocError::Overflow)));
        }
    }

    #[test]
    fn test_alloc_ptr_new_allocate() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            assert!(!alloc_ptr.is_null());

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_allocate() {
        let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();

        unsafe {
            let layout = alloc_ptr.make_layout_unchecked(3);
            let result = alloc_ptr.allocate(layout, OnError::Panic);

            assert!(result.is_ok());
            assert!(!alloc_ptr.is_null());

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must be null")]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_allocate_allocated() {
        let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        unsafe {
            let layout = alloc_ptr.make_layout_unchecked(1);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            assert!(!alloc_ptr.is_null());

            let _ = alloc_ptr.allocate(layout, OnError::Panic);
        }
    }

    #[test]
    fn test_alloc_ptr_allocate_deallocate() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();

            let layout = alloc_ptr.make_layout_unchecked(3);

            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            assert!(!alloc_ptr.is_null());

            alloc_ptr.deallocate(layout);

            assert!(alloc_ptr.is_null());
        }
    }

    #[test]
    fn test_alloc_ptr_memset_zero() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

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

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_store_access() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            assert_eq!(*alloc_ptr.reference(0), 1);
            assert_eq!(*alloc_ptr.reference(1), 2);
            assert_eq!(*alloc_ptr.reference(2), 3);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_access_mut() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            *alloc_ptr.reference_mut(0) = 10;

            assert_eq!(*alloc_ptr.reference(0), 10);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_access_first() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            assert_eq!(alloc_ptr.reference_first(), &1);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_rfo() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            alloc_ptr.store(0, 1);
            alloc_ptr.store(1, 2);

            assert_eq!(alloc_ptr.read_for_ownership(0), 1);

            assert_eq!(*alloc_ptr.reference(1), 2);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_shift_left() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            for i in 0..5 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            alloc_ptr.shift_left(2, 2);

            assert_eq!(*alloc_ptr.reference(0), 1);
            assert_eq!(*alloc_ptr.reference(1), 2);
            assert_eq!(*alloc_ptr.reference(2), 4);
            assert_eq!(*alloc_ptr.reference(3), 5);
            assert_eq!(*alloc_ptr.reference(4), 5);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_move_one() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            alloc_ptr.store(0, 10);
            alloc_ptr.store(1, 20);
            alloc_ptr.store(2, 30);

            alloc_ptr.memmove_one(0, 2);

            assert_eq!(*alloc_ptr.reference(0), 10);
            assert_eq!(*alloc_ptr.reference(1), 20);
            assert_eq!(*alloc_ptr.reference(2), 10);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_alloc_ptr_as_slice_null_ptr() {
        let alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        let slice = unsafe { alloc_ptr.as_slice(0) };
        assert_eq!(slice, &[]);
    }

    #[test]
    fn test_alloc_ptr_as_slice_empty() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            let slice = alloc_ptr.as_slice(0);
            assert_eq!(slice, &[]);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_as_slice() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            let slice = alloc_ptr.as_slice(3);
            assert_eq!(slice, &[1, 2, 3]);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_alloc_ptr_as_slice_mut_null_ptr() {
        let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
        let slice = unsafe { alloc_ptr.as_slice_mut(0) };
        assert_eq!(slice, &mut []);
    }

    #[test]
    fn test_alloc_ptr_as_slice_mut_empty() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            let slice = alloc_ptr.as_slice_mut(0);
            assert_eq!(slice, &[]);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_as_slice_mut() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(i, i as u8 + 1);
            }

            let slice = alloc_ptr.as_slice_mut(3);
            assert_eq!(slice, &mut [1, 2, 3]);

            alloc_ptr.deallocate(layout);
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
            let mut alloc_ptr: AllocationPointer<DropCounter> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(3);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

            for i in 0..3 {
                alloc_ptr.store(
                    i,
                    DropCounter {
                        count: Rc::clone(&drop_count),
                    },
                );
            }

            alloc_ptr.drop_initialized(0);
            assert_eq!(*drop_count.borrow(), 0);

            alloc_ptr.drop_initialized(3);

            assert_eq!(*drop_count.borrow(), 3);

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Drop range must not be empty")]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_drop_range_invalid() {
        unsafe {
            let mut alloc_ptr: AllocationPointer<u8> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);
            alloc_ptr.drop_range(0..0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_alloc_ptr_drop_range() {
        let drop_count = Rc::new(RefCell::new(0));

        unsafe {
            let mut alloc_ptr: AllocationPointer<DropCounter> = AllocationPointer::new();
            let layout = alloc_ptr.make_layout_unchecked(5);
            let _ = alloc_ptr.allocate(layout, OnError::Panic);

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

            alloc_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_alloc_ptr_clone_from() {
        unsafe {
            let mut source: AllocationPointer<u8> = AllocationPointer::new();
            let layout = source.make_layout_unchecked(3);
            let _ = source.allocate(layout, OnError::Panic);

            for i in 0..3 {
                source.store(i, i as u8 + 1);
            }

            let mut target: AllocationPointer<u8> = AllocationPointer::new();
            let _ = target.allocate(layout, OnError::Panic);

            target.clone_from(source.ptr, 3);

            for i in 0..3 {
                assert_eq!(*source.reference(i), *target.reference(i));
            }

            source.deallocate(layout);
            target.deallocate(layout);
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
        let mut source: AllocationPointer<PanicOnClone> = AllocationPointer::new();
        let mut target: AllocationPointer<PanicOnClone> = AllocationPointer::new();
        unsafe {
            let layout = source.make_layout_unchecked(10);
            let _ = source.allocate(layout, OnError::Panic);
            let _ = target.allocate(layout, OnError::Panic);

            let drop_counter = Rc::new(RefCell::new(0));
            for i in 0..10 {
                let value = PanicOnClone {
                    id: i,
                    panic_on: 5,
                    dropped: Rc::clone(&drop_counter),
                };
                source.store(i, value);
            }

            let source_ptr = source.ptr as *const ();
            let target_ptr = &mut target as *mut AllocationPointer<PanicOnClone> as *mut ();

            let result = std::panic::catch_unwind(move || {
                let target = &mut *(target_ptr as *mut AllocationPointer<PanicOnClone>);
                let source = source_ptr as *const PanicOnClone;
                target.clone_from(source, 10);
            });

            assert!(result.is_err());
            assert_eq!(*drop_counter.borrow(), 5);

            source.deallocate(layout);
            target.deallocate(layout);
        }
    }
}
