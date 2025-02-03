mod alloc;
mod map;
#[cfg(test)]
mod tests;
#[macro_use]
mod builder;
mod opt;

// Public exports.
pub use map::{Entry, OmniMap, OmniMapIntoIter};
