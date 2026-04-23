## OmniMap
[![CI](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml/badge.svg)](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml)

An indexed key-value in-memory data store with characteristics of both hashmaps and vectors.

## **Notes**:
Originally designed as a lightweight, indexed key-value store for high-performance parsers and compilers.

The public API is not stable and may change in the future.

No release has been made yet and it is **not** recommended for production use.

## Implementation highlights
- Relatively simple and lightweight implementation.
- Maintains the order in which items are inserted during all operations including: insertion, updating and **removing**.
- Extremely fast access.
- Extremely fast resizing.
- Removing has higher overhead (more or less depending on the variant), especially with large stored entries.