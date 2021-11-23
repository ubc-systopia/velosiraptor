# Example: Xeon Phi SMPT

## Description

The Xeon Phi SMPT sits between the local physical address space of the co-processor
and the system memory, i.e., memory accesses from the Xeon Phi to the host are
translated by the SMPT.

The Xeon Phi has a 40-bit address space, where the upper half of it (512G - 1TB)
is covered by the SMPT.

The SMPT translates addresses at 16GB granularity onto the 64-bit PCI Express address
space (or host address space). Thus, the SMPT has a total of 32 entries each of which
is controlled by a register.

The control registers are memory mapped and located at offset `0x3100` from the
MMIO registers.

The register is 32-bits in size, where
 - bit 0 controls snooping
 - bits 31..2 contain the high bits of the host memory address

## Unit Specification

```vrs, editable
unit Smpt(..) {
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