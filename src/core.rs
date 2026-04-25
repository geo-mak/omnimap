use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::hint::unreachable_unchecked;
use core::mem;
use core::slice::{Iter, IterMut};

use std::collections::hash_map::DefaultHasher;

use crate::entries::{Entries, Entry};
use crate::index::{MapIndex, Tag};
use crate::mem::error::{MemoryError, OnError};
use crate::opt::OnDrop;
use crate::opt::branch_hints::likely;

pub trait EqKey<K: ?Sized> {
    fn eq_key(&self, key: &K) -> bool;
}

impl<B, K> EqKey<K> for B
where
    K: ?Sized + Borrow<B>,
    B: ?Sized + Eq,
{
    #[inline(always)]
    fn eq_key(&self, key: &K) -> bool {
        self == key.borrow()
    }
}

pub(crate) struct FindResult {
    pub(crate) slot: usize,
    pub(crate) entry: usize,
}

impl FindResult {
    #[inline(always)]
    const fn just_slot(slot: usize) -> Self {
        Self {
            slot,
            // Invalid offset used as a sentinel value to indicate absence.
            entry: usize::MAX,
        }
    }

    #[inline(always)]
    pub(crate) const fn entry_exists(&self) -> bool {
        self.entry != usize::MAX
    }
}

/// Stores the fields of the map and allocates/deallocates its pointers.
/// It does't implement `Drop`. Deallocation is manual.
pub(crate) struct CoreMap<K, V> {
    pub(crate) entries: Entries<K, V>,
    pub(crate) index: MapIndex,
    pub(crate) cap: usize,
    pub(crate) len: usize,
    pub(crate) free: usize,
}

impl<K, V> CoreMap<K, V> {
    /// The initial allocation capacity of the map.
    pub(crate) const INIT_TOTAL_CAP: usize = 4;

    #[inline(always)]
    pub(crate) const fn new() -> Self {
        Self {
            // Unallocated pointers.
            entries: Entries::new(),
            index: MapIndex::new(),
            cap: 0,
            len: 0,
            free: 0,
        }
    }

    /// Creates a new allocated instance according the to the specified capacity `cap`.
    ///
    /// Control bytes will not be initialized.
    ///
    /// Error handling depends on the error handling context `on_err`.
    ///
    /// Note: the size of `new_cap` must be greater than `0` and within the range of `isize::MAX`
    /// bytes to be considered a valid size, but successful allocation remains not guaranteed.
    pub(crate) fn new_acquire_uninit(
        cap: usize,
        on_err: OnError,
    ) -> Result<CoreMap<K, V>, MemoryError> {
        unsafe {
            let mut entries = Entries::new();

            let layout = entries.make_layout(cap, on_err)?;

            let mut index = MapIndex::new_acquire_uninit(cap, on_err)?;

            let error_guard = OnDrop::set_on(cap, |cap| index.release_memory(*cap));

            entries.acquire_memory(layout, on_err)?;

            error_guard.set_off();

            let instance = CoreMap {
                index,
                entries,
                cap,
                free: Self::usable_capacity_of(cap),
                len: 0,
            };

            Ok(instance)
        }
    }

    /// Creates a new allocated instance according the to the specified capacity `cap`.
    ///
    /// Control bytes will be initialized.
    ///
    /// Error handling depends on the error handling context `on_err`.
    ///
    /// Note: the size of `new_cap` must be greater than `0` and within the range of `isize::MAX`
    /// bytes to be considered a valid size, but successful allocation remains not guaranteed.
    #[inline(always)]
    pub(crate) fn new_acquire_init(
        cap: usize,
        on_err: OnError,
    ) -> Result<CoreMap<K, V>, MemoryError> {
        let mut instance = Self::new_acquire_uninit(cap, on_err)?;
        unsafe { instance.index.set_tags_free(cap) };
        Ok(instance)
    }

    /// Shrinks or grows the allocated memory space to the specified `new_cap`.
    ///
    /// This function will not copy data from the allocated memory to the new memory.
    ///
    /// Safety:
    /// - The map is already allocated.
    /// - The map must be empty.
    #[inline]
    pub(crate) unsafe fn adjust_unused_layout(
        &mut self,
        new_cap: usize,
        on_err: OnError,
    ) -> Result<(), MemoryError> {
        debug_assert!(self.len == 0);
        let mut core = Self::new_acquire_init(new_cap, on_err)?;

        mem::swap(self, &mut core);

        unsafe { core.release_memory() }

        Ok(())
    }

    /// Shrinks or grows the allocated memory space to the specified `new_cap`.
    ///
    /// This function will copy data from allocated memory to the new memory and
    /// reset the index and rebuild it according to the new capacity.
    ///
    /// On error, the map's state will not be affected.
    ///
    /// Safety: This method should be called only when the map is already allocated.
    pub(crate) unsafe fn adjust_used_layout(
        &mut self,
        new_cap: usize,
        on_err: OnError,
    ) -> Result<(), MemoryError> {
        let mut core = Self::new_acquire_init(new_cap, on_err)?;

        let current_len = self.len;

        unsafe {
            core.entries
                .as_ptr_mut()
                .copy_from_nonoverlapping(self.entries.as_ptr(), current_len);
        };

        core.len = current_len;
        core.free -= current_len;

        // Hash value is pre-computed, so there is no risk of panic.
        core.build_index();

        mem::swap(self, &mut core);

        unsafe { core.release_memory() }

        Ok(())
    }

    /// Reclaims deleted slots if suitable or reserves more capacity according to the load factor.
    ///
    /// This method panics when overflow occurs or when allocation fails.
    ///
    /// This function shall be called only if the map is considered full.
    pub(crate) fn reclaim_or_acquire(&mut self) {
        if self.len < self.cap >> 1 {
            // Reclaiming deleted slots only.
            self.reindex();

            return;
        };

        if likely(self.cap != 0) {
            // Reallocation.
            match Self::allocation_capacity(self.cap, OnError::Panic) {
                Ok(new_cap) => {
                    let next_cap = new_cap.next_power_of_two();
                    match unsafe { self.adjust_used_layout(next_cap, OnError::Panic) } {
                        Ok(_) => (),
                        Err(_) => unsafe { unreachable_unchecked() },
                    }
                }
                Err(_) => unsafe { unreachable_unchecked() },
            }
        } else {
            // New allocation.
            match CoreMap::new_acquire_init(Self::INIT_TOTAL_CAP, OnError::Panic) {
                Ok(mut core) => mem::swap(self, &mut core),
                Err(_) => unsafe { unreachable_unchecked() },
            }
        }
    }

    /// Tries to reserve `additional` memory.
    ///
    /// All internal calls are checked, with result depends on the error handling context `on_err`.
    pub(crate) fn acquire_additional_memory(
        &mut self,
        count: usize,
        on_err: OnError,
    ) -> Result<(), MemoryError> {
        if likely(count != 0) {
            let extra_cap = Self::allocation_capacity(count, on_err)?;

            if likely(self.cap != 0) {
                match self.cap.checked_add(extra_cap) {
                    Some(new_cap) => unsafe { self.adjust_used_layout(new_cap, on_err) },
                    None => Err(on_err.layout_err()),
                }
            } else {
                match Self::new_acquire_init(extra_cap, on_err) {
                    Ok(mut core) => {
                        mem::swap(self, &mut core);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
        } else {
            Ok(())
        }
    }

    /// Calls drop on initialized elements in entries.
    ///
    /// # Safety
    ///
    /// Data must be allocated before calling this method.
    #[inline(always)]
    pub(crate) unsafe fn drop_initialized(&mut self) {
        unsafe { self.entries.drop_initialized(self.len) };
    }

    /// Deallocates index and entries **without** resetting the fields.
    /// It doesn't call drop on initialized items either.
    ///
    /// Safety: Data must be allocated before calling this method.
    #[inline]
    pub(crate) unsafe fn release_memory(&mut self) {
        unsafe {
            let layout = self.entries.make_layout_unchecked(self.cap);
            self.entries.release_memory(layout);
            self.index.release_memory(self.cap);
        }
    }

    #[inline(always)]
    const fn usable_capacity_of(cap: usize) -> usize {
        ((cap >> 3) * 7) + (((cap & 7) * 7) >> 3)
    }

    #[inline(always)]
    pub(crate) const fn usable_capacity(&self) -> usize {
        Self::usable_capacity_of(self.cap)
    }

    /// Returns the value that maintains the load factor for a given capacity `given`.
    ///
    /// **Safety**: This method doesn't check for arithmetic overflow.
    #[must_use]
    #[inline(always)]
    pub(crate) const unsafe fn allocation_capacity_unchecked(given: usize) -> usize {
        ((given + 1) * 8) / 7
    }

    /// Returns the value that maintains the load factor for a given capacity `given`.
    ///
    /// This method checks for arithmetic overflow.
    #[inline(always)]
    pub(crate) const fn allocation_capacity(
        given: usize,
        on_err: OnError,
    ) -> Result<usize, MemoryError> {
        if let Some(plus_one) = given.checked_add(1)
            && let Some(mul_eight) = plus_one.checked_mul(8)
        {
            return Ok(mul_eight / 7);
        }
        Err(on_err.layout_err())
    }

    /// Calculates the hash value for a key.
    ///
    /// > Note: The hash method of the `key` may panic.
    #[inline]
    pub(crate) fn hash<B>(key: &B) -> usize
    where
        B: ?Sized + Hash,
    {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize
    }

    /// Resets and rebuilds the index of the map according to the current entries and the capacity
    /// of the index.
    #[inline(always)]
    fn reindex(&mut self) {
        unsafe { self.index.set_tags_free(self.cap) };
        self.free = self.usable_capacity() - self.len;
        self.build_index();
    }

    /// Builds the index of the map according to the current entries and the capacity of the index.
    /// This method should be called **only** after resetting the index.
    pub(crate) const fn build_index(&mut self) {
        let mut i = 0;
        unsafe {
            while i < self.len {
                let entry = self.entries.reference(i);
                let mut slot = entry.hash % self.cap;

                'probing: loop {
                    let tag = self.index.tag_ref_mut(slot);

                    if tag.is_free() {
                        *tag = Tag::Used;
                        self.index.store_entry_index(slot, i);
                        break 'probing;
                    }

                    debug_assert!(
                        !tag.is_discarded(),
                        "Logic error: detected deleted slot while building index"
                    );

                    slot = (slot + 1) % self.cap;
                }

                i += 1;
            }
        }
    }

    /// Decrements the index of all occupied slots with index value greater than `after` by using
    /// linear search.
    ///
    /// The search domain is `[0, capacity - 1]`.
    const fn decrement_index_linear(&mut self, after: usize) {
        let mut i = 0;
        unsafe {
            while i < self.cap {
                if self.index.load_tag(i).is_used() {
                    let index = self.index.entry_index_ref_mut(i);
                    if *index > after {
                        *index -= 1;
                    }
                }
                i += 1
            }
        }
    }

    /// Decrements the index of occupied slots by using the hash value of each entry after `after`
    /// to find its slot.
    ///
    /// The search domain starts from `after` as exclusive bound and ends with `inc_end` as
    /// inclusive upper bound.
    const fn decrement_index_hash(&mut self, after: usize, inc_end: usize) {
        let mut i = after + 1;
        unsafe {
            while i <= inc_end {
                let hash = self.entries.reference(i).hash;
                let mut slot = hash % self.cap;

                'probing: loop {
                    if self.index.load_tag(slot).is_used() {
                        let index = self.index.entry_index_ref_mut(slot);
                        if *index == i {
                            *index -= 1;
                            break 'probing;
                        }
                    }

                    slot = (slot + 1) % self.cap
                }

                i += 1;
            }
        }
    }

    /// Decrements the index of the occupied slots.
    ///
    /// Parameters:
    ///  - `after`: the position to decrement after it.
    ///  - `inc_end`: an **inclusive** upper bound for decrementing.
    ///
    /// Decrementing applies one of two methods to find the target slots.
    ///
    /// - If `inc_end - after` is greater than `capacity/2`, the search for the affected slots will
    ///   be linear decrementing all encountered occupied slots in the index with value greater than
    ///   `after` within the range `[0, capacity - 1]`.
    ///
    /// - If `inc_end - after` is less than or equal to `capacity/2`, the search for the target
    ///   slots will be very specific using the hash value of the entries starting from offset
    ///   `from + 1` to `inc_end` as an inclusive upper bound.
    #[inline]
    pub(crate) const fn decrement_index(&mut self, after: usize, inc_end: usize) {
        let count = inc_end - after;
        if count > self.cap / 2 {
            self.decrement_index_linear(after);
        } else {
            // It has probing overhead, but it can skip large sequences.
            self.decrement_index_hash(after, inc_end);
        }
    }

    /// Finds the slot of the key in the index.
    ///
    /// If the key already exists, the returned `slot` is the index of its slot and `entry`
    /// is the index of its entry.
    ///
    /// If the key doesn't exist, the returned `slot` is free for inserting and the value
    /// of `entry` is an **invalid** index.
    ///
    /// # Safety
    ///
    /// Before using `entry`, its value must be checked first with `entry_exists()` method,
    /// because its value can be an invalid index.
    pub(crate) fn find<B>(&self, hash: usize, key: &B) -> FindResult
    where
        B: ?Sized + EqKey<K>,
    {
        let mut slot = hash % self.cap;

        unsafe {
            loop {
                match self.index.load_tag(slot) {
                    Tag::Used => {
                        let entry = self.index.load_entry_index(slot);
                        if key.eq_key(&self.entries.reference(entry).key) {
                            return FindResult { slot, entry };
                        }
                    }
                    Tag::Free => return FindResult::just_slot(slot),
                    Tag::Discarded => { /* TODO: Recovering it can save expensive reallocations */ }
                }
                slot = (slot + 1) % self.cap;
            }
        }
    }

    /// Removes an entry by its `key` and returns its value.
    ///
    /// If `SHIFT` is `true`, this method will shift all entries after it to fill the gab, and
    /// updates their slots.
    ///
    /// If `SHIFT` is `false`, this method will copy the last entry to the place of the removed
    /// entry without shifting, and updates its slot.
    ///
    /// # Safety
    ///
    /// Map must not be empty when calling this method.
    #[inline]
    pub(crate) fn remove_entry<B, const SHIFT: bool>(&mut self, key: &B) -> Option<V>
    where
        K: Eq + Borrow<B>,
        B: ?Sized + Hash + Eq,
    {
        let hash = Self::hash(key);

        let result = self.find(hash, key);

        if result.entry_exists() {
            let index = result.entry;

            self.len -= 1;

            // Note: Deleted entries are currently not recoverable so self.free remains unchanged.

            unsafe {
                self.index.store_tag(result.slot, Tag::Discarded);

                // Safety: Keep it alive one piece, no destructors shall run before patching its "hole".
                let removed = self.entries.read_for_ownership(index);

                if likely(index != self.len) {
                    if SHIFT {
                        // Call order matters.
                        self.decrement_index(index, self.len);
                        self.entries.shift_left(index, self.len - index);
                    } else {
                        let last = self.entries.reference(self.len);
                        let swapped = self.find(last.hash, &last.key);
                        self.index.store_entry_index(swapped.slot, index);
                        self.entries.memmove_one(self.len, index);
                    }
                }

                // Safety: The hole is patched. Entry is safe to destructure.
                return Some(removed.value);
            };
        }

        // Key was not found.
        None
    }

    /// Returns an iterator over the current entries.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    #[inline]
    pub(crate) fn iter_entries(&self) -> Iter<'_, Entry<K, V>> {
        if self.len == 0 {
            return [].iter();
        };
        unsafe { self.entries.as_slice(self.len).iter() }
    }

    /// Returns a mutable iterator over the entries in the map.
    ///
    /// This method makes it safe to iterate over the entries without worrying about the state of
    /// the pointer and to trick the compiler to return empty iterator without type inference
    /// issues when used with `map`.
    #[inline]
    pub(crate) fn iter_entries_mut(&mut self) -> IterMut<'_, Entry<K, V>> {
        if self.len == 0 {
            return [].iter_mut();
        };
        unsafe { self.entries.as_slice_mut(self.len).iter_mut() }
    }
}
