## OmniMap

An indexed key-value in-memory data store with characteristics of both hashmaps and vectors.

Originally designed as a lightweight, indexed key-value store for high-performance snappy parsers and compilers.

## **⚠️ Notes**:
- The public API is unstable and it may get changed.

- No release has been made yet and it is **not** recommended for production use.

## Implementation highlights
- Relatively simple and lightweight implementation.
- Maintains the order in which items are inserted during all operations including: insertion, updating and **removing**.
- Extremely fast access.
- Extremely fast resizing.
- Removing has higher overhead (more or less depending on the variant), especially with large stored entries.