## OmniMap
[![CI](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml/badge.svg)](https://github.com/geo-mak/omni_map/actions/workflows/ci.yml)

A key-value data structure with characteristics of both hash maps and vectors.

## **Notes**:
Originally designed as a lightweight, indexed key-value store for high-performance parsers and compilers.

The public API is not stable and may change in the future.

No release has been made yet and it is not recommended for production use.

## Implementation highlights
- Relatively simple and compact implementation that relies mostly on `core` intrinsics.
- Maintains the order in which items are inserted.
- Order preservation of items during all operations including: insertion, updating and **removing**.
- Optimized for fast access.