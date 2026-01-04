use core::alloc::Layout;
use core::hint::unreachable_unchecked;

use crate::AllocError;
use crate::alloc::MemorySpace;
use crate::error::OnError;

/// The state of the slot in the index.
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub(crate) enum Tag {
    Empty = 0,
    Deleted = 1,
    Occupied = 2,
}

impl Tag {
    #[inline(always)]
    pub(crate) const fn is_empty(self) -> bool {
        self as u8 == Tag::Empty as u8
    }

    #[inline(always)]
    pub(crate) const fn is_deleted(self) -> bool {
        self as u8 == Tag::Deleted as u8
    }

    #[inline(always)]
    pub(crate) const fn is_occupied(self) -> bool {
        self as u8 == Tag::Occupied as u8
    }
}

/// A helper type to manage index's memory.
pub(crate) struct MapIndex {
    // -----------------------------------------------------------------------------------
    // |                        The memory layout of the index                           |
    // | |------------ usize * N ------------|---------- u8 * N ------------|- u8 * X -| |
    // | [ IndexN-1 | ... | Index1 | Index0 ]|[ Tag0 | Tag1 | ... | TagN-1 ] [ Padding ] |
    // |                usize strides (-) <- ^ -> (+) u8 strides                         |
    // |                                     |                                           |
    // |                                  Pointer                                        |
    // | Legend:                                                                         |
    // | N: The allocated capacity.                                                      |
    // | X: The required bytes to round the total size to multiple of usize's alignment. |
    // | Tag: A single byte as flag to store slot's state.                               |
    // | Index: The offset of an entry to be accessed at.                                |
    // -----------------------------------------------------------------------------------
    memory: MemorySpace<u8>,
}

impl MapIndex {
    const T_SIZE: usize = size_of::<usize>();
    const T_ALIGN: usize = align_of::<usize>();
    const T_MAX_ALLOC_SIZE: usize = (isize::MAX as usize + 1) - Self::T_ALIGN;

    /// Returns the `(aligned layout, slots size)` of the index for a given capacity `cap`.
    /// Size and alignment are calculated for `usize`.
    ///
    /// This function checks for overflow and valid layout's size.
    #[inline]
    fn index_layout(cap: usize) -> Option<(Layout, usize)> {
        let slots_size = cap.checked_mul(Self::T_SIZE)?;
        let aligned_tags = (cap + Self::T_ALIGN - 1) & !(Self::T_ALIGN - 1);
        let total_size = slots_size.checked_add(aligned_tags)?;
        if Self::T_MAX_ALLOC_SIZE > total_size {
            let layout = unsafe { Layout::from_size_align_unchecked(total_size, Self::T_ALIGN) };
            return Some((layout, slots_size));
        }
        None
    }

    /// Creates new unallocated index.
    #[inline(always)]
    pub(crate) const fn new() -> Self {
        Self {
            memory: MemorySpace::new(),
        }
    }

    /// Creates new instance and allocates memory according to the capacity `cap`, without
    /// initializing control tags.
    ///
    /// Handling of errors will be done according to the error handling context `on_err`.
    #[inline]
    pub(crate) unsafe fn new_allocate_uninit(
        cap: usize,
        on_err: OnError,
    ) -> Result<Self, AllocError> {
        match Self::index_layout(cap) {
            Some((layout, slots_size)) => {
                let mut mem_space = MemorySpace::new();
                unsafe {
                    mem_space.allocate(layout, on_err)?;
                    // Set the pointer at the offset of the control tags.
                    mem_space.set_ptr_plus(slots_size);
                }
                Ok(Self { memory: mem_space })
            }
            None => Err(on_err.overflow()),
        }
    }

    /// Copies bitwise `cap` count values from `source` to `self`.
    ///
    /// # Safety
    ///
    /// - This instance and `source` must be allocated before calling this method.
    /// - `cap` must be the same allocated capacity by both in order to copy data correctly.
    #[inline]
    pub(crate) const unsafe fn copy_from(&mut self, source: &MapIndex, cap: usize) {
        let slots_size = cap * Self::T_SIZE;
        // Copy the useful data without the padding bytes.
        let unaligned_size = slots_size + cap;

        unsafe {
            let source_start = source.memory.ptr().sub(slots_size);
            let self_start = self.memory.ptr().sub(slots_size);
            core::ptr::copy_nonoverlapping(source_start, self_start as *mut u8, unaligned_size)
        }
    }

    /// Resets the pointer to the start of the allocated buffer and deallocates the current index
    /// according to the current capacity.
    ///
    /// # Safety
    ///
    /// - Index must be allocated before calling this method.
    /// - `cap` must be the same allocated capacity.
    #[inline]
    pub(crate) unsafe fn deallocate(&mut self, cap: usize) {
        match Self::index_layout(cap) {
            Some((layout, slots_size)) => {
                unsafe {
                    // Reset the pointer to the start of the allocated memory.
                    self.memory.set_ptr_minus(slots_size);
                    self.memory.deallocate(layout)
                }
            }
            // Already checked when allocated, so it must not fail.
            None => unsafe { unreachable_unchecked() },
        }
    }

    /// Reads and returns the control tag in the index at tag's `offset`.
    ///
    /// # Safety
    ///
    /// - Index must be allocated and control tags must be initialized before calling this method.
    ///
    /// - Safe casting to `Tag` depends on initializing the control tags when allocating and
    ///   reallocating and using `Tag` enum to store tag's value.
    #[inline(always)]
    pub(crate) const unsafe fn read_tag(&self, offset: usize) -> Tag {
        unsafe { self.memory.ptr_as::<Tag>().add(offset).read() }
    }

    /// Stores the control tag at the specified tag's `offset`.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn store_tag(&mut self, offset: usize, tag: Tag) {
        unsafe { self.memory.store(offset, tag as u8) };
    }

    /// Returns a mutable reference to the control tag in the index at tag's `offset`.
    ///
    /// # Safety
    ///
    /// - Index must be allocated and control tags must be initialized before calling this method.
    ///
    /// - Safe casting to `Tag` depends on initializing the control tags when allocating and
    ///   reallocating and using `Tag` enum to store tag's value.
    #[inline(always)]
    pub(crate) const unsafe fn tag_ref_mut(&mut self, offset: usize) -> &mut Tag {
        unsafe { &mut *self.memory.ptr_mut_as::<Tag>().add(offset) }
    }

    /// Reads and returns the slot's value according to the specified tag's `offset`.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn read_entry_index(&self, offset: usize) -> usize {
        unsafe { self.memory.ptr_as::<usize>().sub(offset + 1).read() }
    }

    /// Stores slot's value according to the specified tag's `offset`.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn store_entry_index(&mut self, offset: usize, value: usize) {
        unsafe {
            self.memory
                .ptr_mut_as::<usize>()
                .sub(offset + 1)
                .write(value)
        }
    }

    /// Returns a mutable reference to a slot's value according to the specified tag's `offset`.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn entry_index_ref_mut(&mut self, offset: usize) -> &mut usize {
        unsafe { &mut *self.memory.ptr_mut_as::<usize>().sub(offset + 1) }
    }

    /// Stores the control tag and slot's value at the specified tag's `offset`.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn store(&mut self, offset: usize, tag: Tag, value: usize) {
        unsafe {
            self.store_tag(offset, tag);
            self.store_entry_index(offset, value)
        };
    }

    /// Sets all control tags to empty.
    ///
    /// # Safety
    ///
    /// Index must be allocated before calling this method.
    #[inline(always)]
    pub(crate) const unsafe fn set_tags_empty(&mut self, cap: usize) {
        unsafe { self.memory.memset_zero(cap) }
    }
}

#[cfg(test)]
mod index_tests {
    use crate::opt::OnDrop;

    use super::*;

    #[test]
    fn test_index_layout() {
        let (layout, slots_size) = MapIndex::index_layout(10).unwrap();

        assert_eq!(layout.align(), 8);

        assert_eq!(slots_size, 80);

        // 80 bytes for slots and 10 control tags and 6 padding bytes.
        assert_eq!(layout.size(), 96);
    }

    #[test]
    fn test_index_new() {
        let instance = MapIndex::new();
        assert!(instance.memory.is_null());
    }

    #[test]
    fn test_index_new_allocate_uninitialized() {
        unsafe {
            let mut instance = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            assert!(!instance.memory.is_null());

            instance.deallocate(10)
        }
    }

    #[test]
    fn test_index_allocate_uninitialized_error() {
        unsafe {
            let result = MapIndex::new_allocate_uninit(isize::MAX as usize, OnError::ReturnErr);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_index_store_read_tags() {
        unsafe {
            let mut instance = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            instance.set_tags_empty(10);

            for i in 0..10 {
                assert!(instance.read_tag(i).is_empty());
            }

            for i in 0..10 {
                instance.store_tag(i, Tag::Occupied)
            }

            for i in 0..10 {
                assert!(instance.read_tag(i).is_occupied());
            }

            instance.deallocate(10)
        }
    }

    #[test]
    fn test_index_store_read_entry_index() {
        unsafe {
            let mut instance = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            instance.set_tags_empty(10);

            for i in 0..10 {
                instance.store_entry_index(i, 11)
            }

            for i in 0..10 {
                assert_eq!(instance.read_entry_index(i), 11);
            }

            instance.deallocate(10)
        }
    }

    #[test]
    fn test_index_initialize_from() {
        unsafe {
            let mut source = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            source.set_tags_empty(10);

            for i in 0..10 {
                source.store_tag(i, Tag::Occupied)
            }

            for i in 0..10 {
                source.store_entry_index(i, 11)
            }

            let mut target = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            target.copy_from(&source, 10);

            for i in 0..10 {
                assert!(target.read_tag(i).is_occupied());
            }

            for i in 0..10 {
                assert_eq!(target.read_entry_index(i), 11);
            }

            source.deallocate(10);
            target.deallocate(10)
        }
    }

    #[test]
    fn test_index_reset_control_tags() {
        unsafe {
            let mut instance = MapIndex::new_allocate_uninit(10, OnError::NoReturn).unwrap();

            instance.set_tags_empty(10);

            for i in 0..10 {
                instance.store_tag(i, Tag::Occupied)
            }

            instance.set_tags_empty(10);

            for i in 0..10 {
                assert!(instance.read_tag(i).is_empty());
            }

            instance.deallocate(10);
        }
    }

    #[test]
    fn test_index_scope_guard() {
        unsafe {
            let cap = 10;
            let mut instance = MapIndex::new_allocate_uninit(cap, OnError::NoReturn).unwrap();
            assert!(!instance.memory.is_null());

            {
                let _ = OnDrop::set(cap, |cap| instance.deallocate(*cap));
                // Out of scope, dropped.
            }

            // Deallocated.
            assert!(instance.memory.is_null());
        }
    }

    #[test]
    fn test_index_scope_guard_deactivate() {
        unsafe {
            let cap = 10;
            let mut instance = MapIndex::new_allocate_uninit(cap, OnError::NoReturn).unwrap();
            assert!(!instance.memory.is_null());

            {
                let guard = OnDrop::set(cap, |cap| instance.deallocate(*cap));
                guard.finish();
                // Out of scope.
            }

            // Still allocated.
            assert!(!instance.memory.is_null());
            instance.deallocate(10);
        }
    }
}
