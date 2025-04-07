mod alloc;
mod map;
#[cfg(test)]
mod tests;
#[macro_use]
mod builder;
mod error;
mod opt;

// Public exports.
pub use error::AllocError;
pub use map::{Entry, OmniMap, OmniMapIntoIter};
