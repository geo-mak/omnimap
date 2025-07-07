use core::alloc::Layout;
use core::marker::PhantomData;
use core::ops::Range;
use core::ptr;

use crate::error::{AllocError, OnError};
use crate::opt::branch_prediction::likely;
use crate::opt::OnDrop;
use std::alloc::{self, alloc};

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
const fn debug_assert_allocated<T>(instance: &UnsafeBufferPointer<T>) {
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
const fn debug_assert_not_allocated<T>(instance: &UnsafeBufferPointer<T>) {
    assert!(instance.ptr.is_null(), "Pointer must be null");
}

/// `UnsafeBufferPointer` represents an indirect reference to _one or more_ values of type `T`
/// consecutively in memory.
///
/// `UnsafeBufferPointer` guarantees proper `size` and `alignment` of `T`, when storing or accessing
/// values, but it doesn't guarantee safe operations with measures such as null pointer checks or
/// bounds checking.
///
/// Moreover, it doesn't store any metadata about the allocated memory space, such as the size of
/// the allocated memory space and the number of initialized elements, therefore it doesn't offer
/// automatic memory management.
///
/// The user is responsible for allocating, reallocating, and deallocating memory.
///
/// If `T` is not of trivial type, the user is responsible for calling `drop` on the elements to
/// release resources, before deallocating the memory space.
///
/// Limited checks for invariants are done in debug mode only.
///
/// This pointer uses the registered `#[global_allocator]` to allocate memory.
///
/// Using custom allocators will be supported in the future.
pub(crate) struct UnsafeBufferPointer<T> {
    ptr: *const T,
    _marker: PhantomData<T>,
}

impl<T> UnsafeBufferPointer<T> {
    pub(crate) const T_SIZE: usize = size_of::<T>();
    pub(crate) const T_ALIGN: usize = align_of::<T>();
    pub(crate) const T_MAX_ALLOC_SIZE: usize = (isize::MAX as usize + 1) - Self::T_ALIGN;

    /// Creates a new `UnsafeBufferPointer` without allocating memory.
    ///
    /// The pointer is set to `null`.
    ///
    #[must_use]
    #[inline]
    pub(crate) const fn new() -> Self {
        UnsafeBufferPointer {
            ptr: ptr::null(),
            _marker: PhantomData,
        }
    }

    /// Checks if the `UnsafeBufferPointer` is null.
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
    pub(crate) const unsafe fn duplicate(&mut self) -> UnsafeBufferPointer<T> {
        UnsafeBufferPointer {
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
        // Checked in debug-mode for overflow as part of Rust's assert_unsafe_precondition.
        let size = count.unchecked_mul(Self::T_SIZE);

        // More constrained size check.
        #[cfg(debug_assertions)]
        debug_layout_size_align(size, Self::T_ALIGN);

        // Also checked in debug-mode by assert_unsafe_precondition.
        Layout::from_size_align_unchecked(size, Self::T_ALIGN)
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
                let layout = Layout::from_size_align_unchecked(size, Self::T_ALIGN);
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
    /// For instance, on some systems like linux, overcommit is allowed by default, which means
    /// that the kernel will map virtual memory to the process regardless of the backing memory,
    /// only to invoke the so-called _OOM killer_ later, and the process may become a target for
    /// termination.
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

        let ptr = alloc(layout) as *mut T;

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

        alloc::dealloc(self.ptr as *mut u8, layout);

        self.ptr = ptr::null();
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

        self.ptr as *mut T
    }

    /// Returns the base pointer as a pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn access_as<C>(&self) -> *const C {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr as *const C
    }

    /// Returns the base pointer as a mutable pointer of type `C`.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn access_mut_as<C>(&mut self) -> *mut C {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr as *mut C
    }

    /// Sets the base pointer at current offset plus `t_offset` of the strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn set_plus(&mut self, t_offset: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr = self.ptr.add(t_offset);
    }

    /// Sets the base pointer at current offset minus `t_offset` of the strides of `T`.
    #[inline(always)]
    pub(crate) const unsafe fn set_minus(&mut self, t_offset: usize) {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        self.ptr = self.ptr.sub(t_offset);
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

        ptr::write_bytes(self.ptr as *mut T, 0, count);
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

        ptr::write((self.ptr as *mut T).add(at), value);
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
    pub(crate) const unsafe fn access(&self, at: usize) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        &*self.ptr.add(at)
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
    pub(crate) const unsafe fn access_mut(&mut self, at: usize) -> &mut T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        &mut *(self.ptr as *mut T).add(at)
    }

    /// Returns a reference to the first element.
    ///
    /// # Safety
    ///
    /// This method checks for out of bounds access in debug mode only.
    ///
    /// The caller must ensure that the `UnsafeBufferPointer` is not empty.
    ///
    /// # Time Complexity
    ///
    /// _O_(1).
    ///
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn access_first(&self) -> &T {
        #[cfg(debug_assertions)]
        debug_assert_allocated(self);

        &*self.ptr
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

        ptr::read((self.ptr as *mut T).add(at))
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

        let dst = (self.ptr as *mut T).add(at);
        let src = dst.add(1);

        ptr::copy(src, dst, count);
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

        let src = (self.ptr as *mut T).add(from);
        let dst = (self.ptr as *mut T).add(to);

        ptr::copy(src, dst, 1);
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

        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr as *mut T, count));
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

        ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
            self.ptr.add(range.start) as *mut T,
            range.end - range.start,
        ));
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

        &*ptr::slice_from_raw_parts(self.ptr, count)
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

        &mut *ptr::slice_from_raw_parts_mut(self.ptr as *mut T, count)
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

        // The borrow checker will not allow mutable borrowing after defer.
        let self_ptr = self.ptr as *mut T;

        let cloned = 0;
        let mut drop_guard = OnDrop::set(cloned, |cloned| self.drop_initialized(*cloned));

        for i in 0..clone_count {
            let src = source.add(i);
            let dst = self_ptr.add(i);
            ptr::write(dst, (*src).clone());
            drop_guard.arg += 1; // <- Update.
        }

        // Cloned successfully (If any).
        drop_guard.finish();
    }
}

#[cfg(test)]
mod ptr_tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_buffer_ptr_new() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        assert!(buffer_ptr.is_null());
    }

    #[test]
    fn test_buffer_ptr_make_layout_unchecked_ok() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let layout = buffer_ptr.make_layout_unchecked(3);
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), UnsafeBufferPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_buffer_ptr_make_layout_unchecked_zero_size() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let _ = buffer_ptr.make_layout_unchecked(0);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size exceeds maximum limit on this platform")]
    fn test_buffer_ptr_make_layout_unchecked_invalid_size() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let _ = buffer_ptr.make_layout_unchecked(isize::MAX as usize);
        }
    }

    #[test]
    fn test_buffer_ptr_make_layout_ok() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let layout = buffer_ptr.make_layout(3, OnError::NoReturn).unwrap();
            assert_eq!(layout.size(), 3);
            assert_eq!(layout.align(), UnsafeBufferPointer::<u8>::T_ALIGN);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Allocation size must be greater than 0")]
    fn test_buffer_ptr_make_layout_zero_size_panic() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let _ = buffer_ptr.make_layout(0, OnError::NoReturn);
        }
    }

    #[test]
    #[should_panic(expected = "Allocation Error: capacity overflow")]
    fn test_buffer_ptr_make_layout_overflow_panic() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let _ = buffer_ptr.make_layout(usize::MAX, OnError::NoReturn);
        }
    }

    #[test]
    fn test_buffer_ptr_make_layout_return_err() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let result = buffer_ptr.make_layout(usize::MAX, OnError::ReturnErr);
            assert!(result.is_err());
            assert!(matches!(result, Err(AllocError::Overflow)));
        }
    }

    #[test]
    fn test_buffer_ptr_new_allocate() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Memory space should have been allocated.
            assert!(!buffer_ptr.is_null());

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_allocate() {
        let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();

        unsafe {
            let layout = buffer_ptr.make_layout_unchecked(3);
            let result = buffer_ptr.allocate(layout, OnError::NoReturn);

            assert!(result.is_ok());
            assert!(!buffer_ptr.is_null());

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must be null")]
    #[cfg_attr(miri, ignore)]
    fn test_buffer_ptr_allocate_allocated() {
        let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        unsafe {
            let layout = buffer_ptr.make_layout_unchecked(1);
            // Not yet allocated, should not panic.
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            assert!(!buffer_ptr.is_null());

            // Already allocated, should panic.
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);
        }
    }

    #[test]
    fn test_buffer_ptr_allocate_deallocate() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();

            let layout = buffer_ptr.make_layout_unchecked(3);

            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            assert!(!buffer_ptr.is_null());

            buffer_ptr.deallocate(layout);

            assert!(buffer_ptr.is_null());
        }
    }

    #[test]
    fn test_buffer_ptr_memset_zero() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            for i in 0..3 {
                buffer_ptr.store(i, i as u8 + 1);
            }

            for i in 0..3 {
                assert_ne!(*buffer_ptr.access(i), 0);
            }

            buffer_ptr.memset_zero(3);

            for i in 0..3 {
                assert_eq!(*buffer_ptr.access(i), 0);
            }

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_store_access() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Store some values.
            for i in 0..3 {
                buffer_ptr.store(i, i as u8 + 1);
            }

            assert_eq!(*buffer_ptr.access(0), 1);
            assert_eq!(*buffer_ptr.access(1), 2);
            assert_eq!(*buffer_ptr.access(2), 3);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_access_mut() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Store some values.
            buffer_ptr.store(0, 1);
            buffer_ptr.store(1, 2);

            // Mutate the value.
            *buffer_ptr.access_mut(0) = 10;

            // Value should be updated.
            assert_eq!(*buffer_ptr.access(0), 10);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_access_first() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            buffer_ptr.store(0, 1);
            buffer_ptr.store(1, 2);

            assert_eq!(buffer_ptr.access_first(), &1);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_rfo() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            buffer_ptr.store(0, 1);
            buffer_ptr.store(1, 2);

            assert_eq!(buffer_ptr.read_for_ownership(0), 1);

            assert_eq!(*buffer_ptr.access(1), 2);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_shift_left() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(5);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            for i in 0..5 {
                buffer_ptr.store(i, i as u8 + 1);
            }

            buffer_ptr.shift_left(2, 2);

            assert_eq!(*buffer_ptr.access(0), 1);
            assert_eq!(*buffer_ptr.access(1), 2);
            assert_eq!(*buffer_ptr.access(2), 4);
            assert_eq!(*buffer_ptr.access(3), 5);
            assert_eq!(*buffer_ptr.access(4), 5);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_move_one() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            buffer_ptr.store(0, 10);
            buffer_ptr.store(1, 20);
            buffer_ptr.store(2, 30);

            buffer_ptr.memmove_one(0, 2);

            assert_eq!(*buffer_ptr.access(0), 10);
            assert_eq!(*buffer_ptr.access(1), 20);
            assert_eq!(*buffer_ptr.access(2), 10); // Value at index 2 is overwritten.

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_buffer_ptr_as_slice_null_ptr() {
        let buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        let slice = unsafe { buffer_ptr.as_slice(0) };
        assert_eq!(slice, &[]);
    }

    #[test]
    fn test_buffer_ptr_as_slice_empty() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            let slice = buffer_ptr.as_slice(0);
            assert_eq!(slice, &[]);

            // Deallocate memory space or the destructor will panic.
            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_as_slice() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Store some values.
            for i in 0..3 {
                buffer_ptr.store(i, i as u8 + 1);
            }

            // Values should be accessible as a slice.
            let slice = buffer_ptr.as_slice(3);
            assert_eq!(slice, &[1, 2, 3]);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Pointer must not be null")]
    fn test_buffer_ptr_as_slice_mut_null_ptr() {
        let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
        let slice = unsafe { buffer_ptr.as_slice_mut(0) };
        assert_eq!(slice, &mut []);
    }

    #[test]
    fn test_buffer_ptr_as_slice_mut_empty() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            let slice = buffer_ptr.as_slice_mut(0);
            assert_eq!(slice, &[]);

            // Deallocate memory space or the destructor will panic.
            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_as_slice_mut() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Store some values.
            for i in 0..3 {
                buffer_ptr.store(i, i as u8 + 1);
            }

            // Values should be accessible as a mutable slice.
            let slice = buffer_ptr.as_slice_mut(3);
            assert_eq!(slice, &mut [1, 2, 3]);

            buffer_ptr.deallocate(layout);
        }
    }

    #[derive(Debug)]
    struct DropCounter {
        count: Rc<RefCell<usize>>,
    }

    impl Drop for DropCounter {
        fn drop(&mut self) {
            // Increment the drop count.
            *self.count.borrow_mut() += 1;
        }
    }

    #[test]
    fn test_buffer_ptr_drop_init() {
        let drop_count = Rc::new(RefCell::new(0));

        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<DropCounter> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(3);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Reference 5 elements to the same drop counter.
            for i in 0..3 {
                buffer_ptr.store(
                    i,
                    DropCounter {
                        count: Rc::clone(&drop_count),
                    },
                );
            }

            // Dropping with count 0 is a no-op.
            buffer_ptr.drop_initialized(0);
            assert_eq!(*drop_count.borrow(), 0);

            // Drop all.
            buffer_ptr.drop_initialized(3);

            // `drop` should have been called on all elements, so the drop count must be 3.
            assert_eq!(*drop_count.borrow(), 3);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Drop range must not be empty")]
    #[cfg_attr(miri, ignore)]
    fn test_buffer_ptr_drop_range_invalid() {
        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(5);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);
            buffer_ptr.drop_range(0..0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_buffer_ptr_drop_range() {
        // Drop counter with 0 count initially.
        let drop_count = Rc::new(RefCell::new(0));

        unsafe {
            let mut buffer_ptr: UnsafeBufferPointer<DropCounter> = UnsafeBufferPointer::new();
            let layout = buffer_ptr.make_layout_unchecked(5);
            let _ = buffer_ptr.allocate(layout, OnError::NoReturn);

            // Reference 5 elements to the same drop counter.
            for i in 0..5 {
                buffer_ptr.store(
                    i,
                    DropCounter {
                        count: Rc::clone(&drop_count),
                    },
                );
            }

            // Drop 3 elements in the range [0, 3 - 1].
            buffer_ptr.drop_range(0..3);

            // Since the `drop` has been called on 3 elements, the drop count must be 3.
            assert_eq!(*drop_count.borrow(), 3);

            buffer_ptr.deallocate(layout);
        }
    }

    #[test]
    fn test_buffer_ptr_clone_from() {
        unsafe {
            let mut source: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let layout = source.make_layout_unchecked(3);
            let _ = source.allocate(layout, OnError::NoReturn);

            for i in 0..3 {
                source.store(i, i as u8 + 1);
            }

            let mut target: UnsafeBufferPointer<u8> = UnsafeBufferPointer::new();
            let _ = target.allocate(layout, OnError::NoReturn);

            target.clone_from(source.ptr, 3);

            for i in 0..3 {
                assert_eq!(*source.access(i), *target.access(i));
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
    fn test_buffer_ptr_clone_from_safe_unwind() {
        let mut source: UnsafeBufferPointer<PanicOnClone> = UnsafeBufferPointer::new();
        let mut target: UnsafeBufferPointer<PanicOnClone> = UnsafeBufferPointer::new();
        unsafe {
            let layout = source.make_layout_unchecked(10);
            let _ = source.allocate(layout, OnError::NoReturn);
            let _ = target.allocate(layout, OnError::NoReturn);

            let drop_counter = Rc::new(RefCell::new(0));
            for i in 0..10 {
                let value = PanicOnClone {
                    id: i,
                    panic_on: 5,
                    dropped: Rc::clone(&drop_counter),
                };
                source.store(i, value);
            }

            // Camouflage to enter the catch_unwind block without safety complains.
            let source_ptr = source.ptr as *const ();
            let target_ptr = &mut target as *mut UnsafeBufferPointer<PanicOnClone> as *mut ();

            let result = std::panic::catch_unwind(move || {
                // Cast back to typed pointers.
                let target = &mut *(target_ptr as *mut UnsafeBufferPointer<PanicOnClone>);
                let source = source_ptr as *const PanicOnClone;
                // Here we go...
                target.clone_from(source, 10);
            });

            assert!(result.is_err());
            assert_eq!(*drop_counter.borrow(), 5);

            source.deallocate(layout);
            target.deallocate(layout);
        }
    }
}
