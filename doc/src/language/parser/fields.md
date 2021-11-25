# Fields

A field defines a part of a state (or similarly an element of an interface), gives it
a name, and describes its bit pattern. Fields have a specific size.

There are two field descriptions: another for memory (with a base-offset component), and
one for registers (without base-offset component).


## Grammar

```
MEMORY_FIELD_BLOCK     :=  "{" MEMORY_FIELD+ "}"
REGISTER_FIELD_BLOCK   :=  "{" REGISTER_FIELD+ "}"

MEMORY_FIELD           :=  IDENT MEMORY_FIELD_PARAMS BITSLICE_BLOCK? ";"
REGISTER_FIELD         :=  IDENT REGISTER_FIELD_PARAMS BITSLICE_BLOCK? ";"

MEMORY_FIELD_PARAMS    :=  "[" IDENT "," NUM "," NUM "]"
REGISTER_FIELD_PARAMS  :=  "[" NUM "]"

BITSLICE_BLOCK         := "{" BITSLICE+ "}"
BITSLICE               := NUM NUM IDENT ";"
```

## Examples

Example of a memory field "address" of size `8` bytes at `base + 0`
```vrs
address [base, 0, 8] {
    0  63 base
};
```

Example of a register field "length" of size `4` bytes, and two slices.
```vrs
length [4] {
    0  15 count;
    15 31 multiplier;
};
```

Example of a memory field "address" of size `8` bytes at `base + 8` without slices;
```vrs
address [base, 8, 8];
```

## Field Blocks

Within a field block of a state or interface definition, each field must have a unique identifier,
and they must not overlap.

## Field Parameters

**Memory Field Parameters**
The meaning of the memory field parameters is `[base, offset, length]` where
`offset` and `length` are in bytes, and `base` is an identifier to the memory region holding the
state.

The identifier must be defined in the argument list of the state or interface.

**Register Field Parameters**
The meaning of the memory field parameters is `[length]` where `length` is in bytes.

**Length**
The length of the field must be `1`, `2`, `4`, or `8`.


## Bitslices

Within a field, each bitslice must have a unique identifier and must not overlap with
any other bitslice.

**Bitslice Definition**
The meaning of the bitslice is `start end identifier` or `end start identifier`,
where `start` and `end` are in bits.

The start and end bits must not exceed the available bits of the enclosing field.

To denote a single bit, set the `start == end` bit.
