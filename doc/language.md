# The VelosiRaptor Specification Language

This document describes the VelosiRaptor Specification Language and its
elements. The language is designed to intuitively describe address translation
hardware, including its translation semantics, state and software visible
interface. The language serves as a basis for generating both, an OS driver
and a (simulated) hardware component implementing the translation hardware.


## Basic Constructs

We first define the basic building blocks of the keywords such as keywords,
identifiers and so on.

First, we define the following basic sets of characters for expressing the
language lexemes.

```
    NUMERIC      := [ 0-9 ]
    ALPHA        := [ a-zA-Z ]
    ALPHANUMERIC := [ :ALPHA: | :NUMERIC: ]
```

The identifier is then a letter, followed by zero or more alphanumeric
characters.

```
IDENTIFIER := [ :ALPHA: ]  [ :ALPHANUMERIC: ]*
```

## Keywords

The language has the following keywords

```
    unit
    import
    memory
    register
    map
```

## Specification Files

The VelosiRaptor Specification Language is stored in "VelosiRaptor Specification" files
with the extension `*.vrs`. The files should be standard ASCII and use UNIX-style new
lines (`\n`). The files contain two language constructs: `import` statements and `unit`
definitions.

Example:

```
    example.vrs
```

## Import Statements

The VelosiRaptor provides features to import definitions from other VelosiRaptor
Specification Files. This provides functionality for modular and reusable definitions.
The VelosiRaptor compiler will recursively parse the imported files and add the
defined types to the parse state. Currently, we use simple imports such as:

Example:
```
    import table;
```

In the future we may add functionality to do more selective imports such as listing
the types / definitions we are interested in.
```
    from table import L1;
    import table::L1;
```

## Unit Definitions

The unit specifies a translation. It composes previously defined units, base types,
or extends them (see Inheritance).

```
unit L1Table {
    ... // TODO: add the constructs here
};
```

Conceptually, the `unit` translates between an *input* and *output* address space. We
assume that the sizes of these address spaces have a specific amount of bits. Thus,
the size of both input and output address spaces are a power of two.

```
              +----------+
    ---32---> |   unit   | ---32--->
              +----------+
```

A unit has the following components or features:
 1. defines a type
 2. translate: defines how addresses are translated by the unit


Additionally, if the unit is configurable then the unit has two additional features.

 1. state: represents state of the unit and defines the translation behavior. State may be
    one or more registers, memory locations (e.g., DRAM), internal storage. The translation
    unit can access the entire state at will.
 2. interface: defines the software accessible/usable interface. This may be the full state,
    part of it, or even some separate register/memory interface.

Depending on its applicability, the following functions are being generated / synthesized.
Note, this is not just limited to the configurable units, but also static ones that are
composed of configurable units. Calling those functions on the composition will forward
the request to the right configurable unit.

 1. map: installs a new mapping
 2. unmap: removes a mapping
 3. protect: changes the protection bits or properties
 4. get: returns the configurable unit at the address.

 Finally, as part of future work the unit may also include some OS-specific functionality.
 This may include storing meta-data information. We do not go further into these details.

 TODO: abstract units as templates?

## Extending Types (Inheritance)

The language supports extending existing types or inheritance. The new type will include
possible components of the base type. Parts of it can be overridden or must be provided
to achieve the desired functionality.

For example, a page table entry may be derived from the segment base type.

```
unit L1TableEntry : Segment {
    ...
};
```

## Configurable Segments

The configurable segment is an abstract, internal base unit. It basically defines a templated
way how it translates addresses: If the address falls within the size and matches the flags or
properties, then it translates it as `inaddr + base`. The wholes (or methods to be provided)
are:

 1. get_base: obtains the base address of the segment from the state
 2. get_size: obtains the size of the segment from the state
 3. match_flags: checks whether the access flags of the request permit the translation.

Conceptually, the abstract segment provides the following *abstract* unit definition:

```
abstract unit Segment {

    abstract get_base(st);
    abstract get_size(st);
    abstract match_flags(st, flags);

    translate(inaddr, flags) {
        if (!match_flags(st, flags)) {
            raise translation_fault;
        }

        if (inaddr >= get_size()) {
            raise translation_fault;
        }

        return get_base(st) + inaddr;
    };
};
```

Note, strictly speaking this does not need to be used as a base type and a segment can
be defined without the use of the `Segment` base type. However, it might be helpful for
the synthesis / compiler / hardware backend to know that this is a segment.

## Associative

TODO: focus first on the segment and the maps

## Static Maps

A static map divides the input address space and maps ranges of addresses to other
ranges, or units. The most flexible map is basically a non-overlapping list of
base-limit pairs, and where they map to. The region shall be a power of two in size.

Constraint: destination unit size must be greater or equal to the region that is mapped.
Constraint: no overlap.
```
[
    0x0000..0x0fff  ->  UNIT @ 0x1000
    // here is a hole
    0x2000..0x2fff  ->  UNIT
    // here is another hole
]
```

Now this spans the address space with holes. However, often there are no holes and
the entire address range is mapped. So we can leave out the limit part and the limit
is given implicitly.

```
[
    0x0000 -> UNIT
    0x2000 -> UNIT
]
```

Lastly, dividing the input address range into equal chunks is often used. For
example, the page table divides the input range into equal chunks each of which
maps onto an entry

constraint: all units must have the same size ?
constraint: sum of the sizes of all units must be a power of two.

```
    [ UNIT, UNIT, UNIT, UNIT  ]
```

Syntactic sugar:
```
[ UNIT(base + i * 8) for i in 0..512 ]
```

## Expressing State

The state of the translation unit defines how it translates incoming memory accesses.
This can either one of, or a combination of registers or in-memory data structures.
For example, a page table resides in DRAM, where the semantics of some bits in the page table
entry may depend on certain register values (e.g., memory protection key attributes on
x86)

Moreover, the state might be parameterized. That is, some length of the

Finally, the state may or may not be fully observable by software. This means it can be
that there are specific operations to modify the state. See Interfaces.

We define the state as a bitmap with various fields. There are two types of state

1. Memory: the state is at a particular address in memory (e.g., page tables)
2. Registers: the state is a register residing on the translation hardware

The state is a collection of contiguous regions, each having a set of fields at locations
relative to the region. A field has bit slices with specific meaning.

```
STATE_ENTRY_FIELD = nat nat ident

STATE_ENTRY = ident [ident, nat, nat ] {
                [STATE_ENTRY_FIELD]+
              };

REGISTER_STATE = Registers {
                    [STATE_ENTRY]+
                };

MEMORY_STATE =  Memory([ident]+) {
                    [STATE_ENTRY]+
                };

STATE = MEMORY_STATE | REGISTER_STATE
```

Example:

```
    // a single memory region
    Memory(base) {
        // one entry named 'pte' at offset 0, length 4 bytes
        pte [base, 0, 4] {
            // the following fields at starting bit, ending bit, name
            0   0 present
            1   1 writable
            2   2 usersmode
            3   3 writethrough
            4   4 nocache
            5   5 accessed
            6   6 dirty
            7   7 pat
            8   8 global
            9  11 ignored
           12  31 base
        };
```



## Expressing Interfaces

The interface defines the way software can interact with the translation unit. This may be through
reading/writing a specific or variable location in memory or registers, or using a more 'protocol'
like way where the state cannot be fully observed by software.

There are two basic types of interfaces:

 1. Load/Store Memory: software reads/writes a memory location using normal load/store instructions.
                       This triggers an update to the memory location.

 2. Register: software accesses the register either through normal load/store instructions in the
              case of a memory-mapped register, or through special instructions. In contrast to
              loads/stores to a memory location, writing to a register may trigger multiple state
              transitions (e.g., resetting the device)

To some extent, there is a mapping from the interface to the state. This may cover the entire state,
parts of it, or nothing at all. The latter is the case when there is a slightly more sophisticated
protocol requires. For example, write base, write size, write index then triggers a transfer from
the base and size registers to the internal state at index.

The simplest forms of the interface is a direct mapping that exposes the full state. This will
create an interface that maps the state description above. A good example here would be Barrelfish's
Mackerel language.

```
    // direct memory reads/writes to the entire state in memory
    MemoryLoadStoreInterface(state, direct);

    // direct memory reads writes to the entire state in mmio registers
    RegisterLoadStoreInterface(state, direct);
```

It could be that there are special ways to access the register, i.e., there is not just a load/store
to an address backed by a register, but more of a thing

```
    // direct special instruction access to the entire state in special registers
    RegisterInterface(state, direct);
```


In the case that there is not a simple one-to-one correspondence, or there are multiple actions
that are being triggered when writing to a register.

TODO.




## Specifying Translation Semantics


## Adding Constraints


## Complete Examples

### x86 Page Table

32-bit paging on the x86 architecture involves a two-level page table. For simplicity, we focus
here on the leaf page table.

A single page table is 4 KiB in total. It contains 1024 32-bit page-table entries.
The page table as a whole must be naturally aligned (4 KiB).
This also ensures that each entry is naturally aligned to 32-bits (or 4 bytes)

The layout of a page table entry is as follows:
```
    Bit(s)          Contents
    0       (P)     Present; must be 1 to map a 4-KByte page
    1       (R/W)   Read/write; if 0, writes may not be allowed to the 4-KByte page referenced
                    by this entry
    2       (U/S)   User/supervisor; if 0, user-mode accesses are not allowed to the 4-KByte
                    page referenced by this entry
    3       (PWT)   Page-level write-through; indirectly determines the memory type used to
                    access the 4-KByte page referenced by this entry
    4       (PCD)   Page-level cache disable; indirectly determines the memory type used to
                    access the 4-KByte page referenced by this entry
    5       (A)     Accessed; indicates whether software has accessed the 4-KByte page referenced
                    by this entry
    6       (D)     Dirty; indicates whether software has written to the 4-KByte page referenced by
                    this entry
    7       (PAT)   If the PAT is supported, indirectly determines the memory type used to access
                    the 4-KByte page referenced by this entry; otherwise, reserved (must be 0) 1
    8       (G)     Global; if CR4.PGE = 1, determines whether the translation is global;
                    ignored otherwise
    11:9    (IGN)   Ignored
    31:12           Physical address of the 4-KByte page referenced by this entry
```


 * **State:** a single entry is represented as a 32-bit, naturally-aligned location in memory.
 * **Interface:** load/store interface to memory location, atomically updated.

```

// here we have an x86 page table entry, that behaves as a segment
unit x86_pte : segment {
    // the state
    state = Memory(base) {
        // one entry named 'pte' at offset 0, length 4 bytes
        pte [base, 0, 4] {
            // the following fields at starting bit, ending bit, name
            0   0 present
            1   1 writable
            2   2 usersmode
            3   3 writethrough
            4   4 nocache
            5   5 accessed
            6   6 dirty
            7   7 pat
            8   8 global
            9  11 ignored
           12  31 base
        };

    // the intderface is just a load/store
    interface = LoadStoreMemory();

    // the state is given by a external memory reference (we don't know where it's located at)
    // so the state will be a memory reference
    x86_pte(state : ref@memory) {
        // the state must be aligned properly
        assert(aligned(state, 4));
        assert(size(state, 4));
        //
        st = Memory(state);
    }

    // translation is  if (flags match) {addr + base} else {raise}
    get_base(st : state) {
        return st.pte.page << 12;
    }

    // here the size is fixed
    get_size(st : state) {
        return 4096;
    };

    // matches a translation flags,
    match_flags(st, flags) {
        if (st.pte.present == 0) {
            return false;
        }

        if (flags.write && !st.pte.write) {
            return false;
        }

        if (flags.user && !st.pte.user) {
            return false;
        }

        return true;
    };

    // constraints for the mapping
    map(addr, flags) {
        assert (aligned(addr, 4096));
        assert (type(addr) == Memory)
    }

    // constraints for unmapping
    unmap();

    // constraints for protecting
    protect();

};

unit x86_pt {

    state = {

    };

    interface = {};

    translate(inaddr, flags) {

    };



};

```


### x86_64 Page Table


```
    Bit(s)          Contents
    0       (P)     Present; must be 1 to map a 4-KByte page
    1       (R/W)   Read/write; if 0, writes may not be allowed to the 4-KByte page referenced
                    by this entry
    2       (U/S)   User/supervisor; if 0, user-mode accesses are not allowed to the 4-KByte
                    page referenced by this entry
    3       (PWT)   Page-level write-through; indirectly determines the memory type used to
                    access the 4-KByte page referenced by this entry
    4       (PCD)   Page-level cache disable; indirectly determines the memory type used to
                    access the 4-KByte page referenced by this entry
    5       (A)     Accessed; indicates whether software has accessed the 4-KByte page
                    referenced by this entry
    6       (D)     Dirty; indicates whether software has written to the 4-KByte page referenced by
                    this entry
    7       (PAT)   Indirectly determines the memory type used to access the 4-KByte page referenced
                    by this entry
    8       (G)     Global; if CR4.PGE = 1, determines whether the translation is global;
                    ignored otherwise
    11:9    (IGN)   Ignored
    (M–1):12        Physical address of the 4-KByte page referenced by this entry
    51:M    (MBZ)   Reserved (must be 0)
    58:52   (IGN)   Ignored
    62:59   (PK)    Protection key; if CR4.PKE = 1 or CR4.PKS = 1, this may control the page’s
                    access rights; otherwise, it is not used to control access rights.
    63      (XD)    If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed
                    from the 4-KByte page controlled by this entry); otherwise, reserved (must be 0)
```

