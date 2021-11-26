# State

The state defines how a translation hardware unit translates memory addresses, i.e.,
its translation behavior is a function over the state. Conceptually, the state
consist of a set of fields, where each field has bitslices assigning meaning
to a range of bits. The state can be located inside the translation hardware
(i.e., in some registers), or external to it (i.e., in some memory).

## Grammar

```
STATE              := MEMORY_STATE | REGISTER_STATE | NONE_STATE

MEMORY_STATE       := "Memory" "(" ARGLIST ")" MEMORY_FIELD_BLOCK
REGISTER_STATE     := "Register" REGISTER_FIELD_BLOCK
NONE_STATE         := "None"

ARGLIST            := [ ARG [ "," ARG ]* ]
ARG                := IDENT ":" TYPE

```

## Example

```vrs
Memory(base : addr) {
    address [base, 0, 8] {
        0  63 base;
    };
    sz [base, 8, 8] {
        0  63 bytes;
    };
    flags [base, 16, 8] {
        0 0 present;
    };
}

Register {
    foo [8];
    bar [4];
}
```

## External State (Memory State)

External state (or memory state) utilizes some region of main memory to hold translation
information. One prime example for external state would be the page table: the location
of the page table is *external* to the translation hardware that itself issues load/stores
to memory to read (and write) the data structure.

This state is fully visible to system software.

To perform a translation, the translation hardware will interpret a memory location
identified by some *base pointer* and performs address transformation depending on the
contents of this memory location. This base pointer is given by the argument list.

For example, the bit pattern of a page table entry defines whether there exists
a valid translation, and whether the translation points to another page table or to
a physical frame.

All arguments must also be declared as arguments on the unit level.


## Internal State (Register State)

Internal state (or register state) utilizes some form of memory inside the translation
hardware to hold the current translation state. In contrast to the in-memory state,
the actual layout of the internal state representation may not be strictly defined.

This state is not directly visible to system software. Hardware may expose the state
(or parts of it) through a register interface.

To perform a translation, the translation hardware uses the internal state to determine
the translation function.

In contrast to the external state, there is no base pointer.

For example, the contents of the system control register defines whether the
translation hardware is activated or not.


# Fields

Within a state definition, each field must have a unique identifier.

In the memory state, the field parameter must be declared in the argument list.