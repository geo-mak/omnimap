use core::ptr;

/// Debug-mode check for the valid alignment.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - `align` of `T` must not be zero.
///
/// - `align` of `T` must be a power of two.
#[cfg(debug_assertions)]
pub(crate) const fn debug_assert_valid_alignment(align: usize) {
    assert!(align.is_power_of_two(), "Alignment must be a power of two");
}

/// Debug-mode check for the valid allocation size.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - `size` must be greater than `0`.
#[cfg(debug_assertions)]
pub(crate) const fn debug_assert_non_zero_size(size: usize) {
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
pub(crate) const fn debug_layout_size_align(size: usize, align: usize) {
    debug_assert_valid_alignment(align);
    debug_assert_non_zero_size(size);
    assert!(
        ((isize::MAX as usize + 1) - align) >= size,
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
pub(crate) const fn debug_assert_not_null<T>(ptr: *const T) {
    assert!(!ptr.is_null(), "Pointer must not be null");
}

/// Debug-mode check to check the allocation state.
/// This function is only available in debug builds.
///
/// Conditions:
///
/// - The pointer must be null.
///
#[cfg(debug_assertions)]
pub(crate) const fn debug_assert_is_null<T>(ptr: *const T) {
    assert!(ptr.is_null(), "Pointer must be null");
}

/// Sets the pointer to null.
/// This function is only available in debug builds.
///
#[cfg(debug_assertions)]
pub(crate) const fn debug_set_null_mut<T>(ptr_ref: &mut *mut T) {
    *ptr_ref = ptr::null_mut();
}
