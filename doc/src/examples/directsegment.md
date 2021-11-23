# Direct Segment

This translation hardware models a [direct-segment-like](https://research.cs.wisc.edu/multifacet/papers/isca13_direct_segment.pdf) translation
scheme.

## Description

The direct segment is a single, continuous address range controlled
by three 64-bit registers. The region must be between 4G and 128TB,
and must be aligned to 16 bytes.


**VABase**
The base address of the virtual region covered by the direct segment.

**Size**
The size of the region should be aligned to 16 bytes. A size of 0
disables translation.

**DstBase**
The destination region must be within the available 46-bits of
physical addresses, and should be 16 bytes aligned.

**Register Accesss**
The registers are special CPU registers that can be accessed
using load/stores (e.g., `mov rax vabase`).

## Unit Specification

```vrs, editable
unit DirectSegment(..) {
    ..
}
```

## Generated Code

**Rust Code**
```rust
// nothing here yet
```

**C Code**
```c
// nothing here yet
```