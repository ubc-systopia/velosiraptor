# State

The state defines how a translation hardware unit translates memory addresses, i.e.,
its translation behavior is a function over the state. Conceptually, the state
consist of a set of fields, where each field has *bitslices* assigning meaning
to a range of bits. The state can be located inside the translation hardware,
or external to it (i.e., in some memory).

## Grammar

```
STATE := MEMORY_STATE | REGISTER_STATE | NONE_STATE

MEMORY_STATE       := KW_MEMORY LPAREN ARGLIST RPAREN FIELD_BLOCK
REGISTER_STATE     := KW_REGISTER FIELD_BLOCK
NONE_STATE         := KW_NONE

FIELD_BLOCK        := LBRACE [ FIELD ]+ RBRACE
FIELD              := IDENT FIELD_PARAMS BITSLICE_BLOCK? SEMICOLON
FIELD_PARAMS       := LBRACK [IDENT COMMA NUM COMMA ]? NUM RBRACK

BITSLICE_BLOCK     := LBRACE BITSLICE RBRACE
BITSLICE           := NUM NUM IDENT

ARGLIST            := [ ARG [COMMA ARG]* ]?
ARG                := IDENT COLON TYPE

```

## Example

```vrs
Memory(base : addr) {
    address [base, 0, 8] {
        0  63 base
    };
    sz [base, 8, 8] {
        0  63 bytes
    };
    flags [base, 16, 8] {
        0 0 present
    };
};
```

## External State

External state (or memory state) utilizes some region of main memory to hold translation
information. One prime example for external state would be the page table: the location
of the page table is *external* to the translation hardware that itself issues load/stores
to memory to read (and write) the data structure.

This state is fully visible to system software.

To perform a translation, the translation hardware will interpret a memory location
identified by some base pointer and performs address transformation depending on the
contents of this memory location.

For example, the bit pattern of a page table entry defines whether there exists
a valid translation, and whether the translation points to another page table or to
a physical frame.


## Internal State

Internal state (or register state) utilizes some form of memory inside the translation
hardware to hold the current translation state. In contrast to the in-memory state,
the actual layout of the internal state representation may not be strictly defined.

This state is not directly visible to system software. Hardware may expose the state
(or parts of it) through a register interface.

To perform a translation, the translation hardware uses the internal state to determine
the translation function.

For example, the contents of the system control register defines whether the
translation hardware is activated or not.


## Fields

Within a state definition, each field must have a unique identifier.

The identifiers in the `FIELD_PARAM` block must be defined in the field `ARGLIST`

The identifiers in the field `ARGLIST` must be defined in the unit `ARGLIST`

The two numbers indicate offset from base, and the size of the field in bytes.

The size of the field must be `1`, `2`, `4`, or `8`.

## Bitslices

Within a field, each bitslice must have a unique identifier.

The two numbers indicate the start and end (including) bits of the slice.

To denote a single bit, set the `start == end` bit.

The bit slices must not overlap

The bit slices must not exceed the size of the field.