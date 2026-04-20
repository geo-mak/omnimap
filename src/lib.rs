mod mem;
mod map;
#[cfg(test)]
mod tests;
#[macro_use]
mod builder;
mod index;
mod opt;

// Public exports.
pub use mem::error::AllocError;
pub use map::{
    EntriesIterator, EntriesIteratorMut, Entry, KeysIterator, OmniMap, OmniMapIterator,
    ValuesIterator, ValuesIteratorMut,
};
