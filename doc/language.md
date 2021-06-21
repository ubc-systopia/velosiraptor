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

The unit specifies a translation. It composes previously defined units, or base types.

```
unit L1Table {
    ...
};
```

## Extending Types (Inheritance)

The VelosiRaptor specification language has two abstract, configurable base types:

 * `Segment`
 * `Assoc`


```
unit L1TableEntry : Segment {
    ...
};
```

```
unit BridgeWindow : Assoc {
    ...
};
```


Likewise, we can also extend previously defined types.

## Configurable Segments

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

## Static Maps


## Expressing State


## Translation Semantics


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


**State:** a single entry is represented as a 32-bit, naturally-aligned location in memory.
**Interface:** load/store interface to memory location, atomically updated.

```

// here we have an x86 page table entry, that behaves as a segment
unit x86_pte : segment {
    // the state
    state = Memory(base) {
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

    interface = LoadStoreMemory();

    // the state is given by a external memory reference (we don't know where it's located at)
    // so the state will be a memory reference
    x86_pte(state : ref@memory) {
        // the state must be aligned properly
        assert(aligned(state, 4));
        assert(size(state, 4));
        //
        st = state;
    }

    // translation is  if (flags match) {addr + base} else {raise}
    get_base(st : state) {
        return st.page << 12;
    }

    // here the size is fixed
    get_size(st : state) {
        return 4096;
    };

    // matches a translation flags,
    match_flags(st, flags) {
        if (st.present == 0) {
            return false;
        }

        if (flags.write && !st.write) {
            return false;
        }

        if (flags.user && !st.user) {
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

