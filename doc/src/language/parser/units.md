# Units

The unit is the core part of the specification. It combines the [state](state.md), the
[interface](interface.md) and [translation semantics](translate.md) to build a model
of the translation hardware unit and how it translates input addresses.

Note, a complete translation scheme (e.g., an x86 memory management unit) is expressed as a
*collection* of units each of which modeling a specific aspect of it (e.g, a page table entry
at a specific level). The full specification is a *composition* of these units (e.g.,
a page table is a composition of 512 page table entries).

```
                        interface
                            |
                            v
                +-----------------------+
  input addr    |                       |  output addr
 -------------> | translate(input addr) | ------------->
                |                       |
                +-----------------------+
                          unit
```

Conceptually, a unit *translates* an input address to an output address -- analogous (but not limited)
to a virtual to physical address translation. There are *two* distinct translation behaviors:

 1. The **[static map](#static-map-units)** defines a *fixed* translation function known at compile time.
 2. The **[configurable segment](#configurable-segment-units)** defines a configurable translation function that depends
    on the runtime *state*.

Thus, to model a translation unit one needs to find a representation in terms of a combination
of static maps and configurable segments.

In the page table example, the page table as a whole is a fixed mapping of an input address
onto one of the 512 entries, and in turn each entry is a configurable unit defining the
translation of the page depending on the *state* of the entry.


## Grammar

```
UNIT         := KW_UNIT LPAREN ARGLIST RPAREN UNIT_DERIVE LBRACE UNIT_BODY RBRACE

UNIT_DERIVE  := COLON IDENT
UNIT_BODY    := CONST*  STATE?  INTERFACE?  MAP?  METHOD*

ARGLIST      := [ ARG [COMMA ARG]* ]?
ARG          := IDENT COLON TYPE
```

## Example

```vrs
unit Simple(base : addr) : Segment {
    // the state
    state = ...

    // the interface
    interface = ...

    // translation semantics
    fn translate(va: addr, flags: int) -> addr
        ...

    // unmapping an entry
    fn unmap(va: addr, sz: size) -> bool
        ...

    // mapping an entry
    fn map(va: addr, sz: size, flags: int, pa : addr) -> bool
        ...

    // protecting the entry, i.e., change its permission
    fn protect(flags: int) -> bool
        ...
};
```

## Static Map Units

Conceptually, the static map unit type defines a list of input address ranges. Each range
has a well-defined mapping onto either an output address range or another unit.

This modifies the address in the following way:

```
OUT = IN - REGION_BASE + OFFSET
```
This normalizes the address to be translated, i.e., it falls within `[OFFSET, OFFSET + REGION_SIZE)`. For example, an x86_64 page table is a static map of 512 ranges each of which
has size 4096. A page-table entry in turn translates a range `[0, 4096)`.


## Configurable Segment Units

Configurable units are abstracted as a *segment*, i.e., a range of addresses `[0, size)`
that map to an output range `[pa, pa + size)`.

This modifies the address in the following way:

```
OUT = IN + BASE
```


## Unit Components

The following table outlines the main components and which unit type they are required for.

| Component         | Required for                |
|-------------------|-----------------------------|
| State             | Configurable Units          |
| Interface         | Configurable Units          |
| Map               | Static Units                |
| Translate         | Configurable Units          |
| Map/Unmap/Protect | Maybe both                  |


**State Description**
A *configurable* unit has a [state description](state.md). The state of the unit defines
its translation behavior. Methods can reference the state through the `state` symbol.

**Interface Description**
A *configurable* unit has an [interface description](interface.md). The interface defines
how software can interact with the unit to change its translation behavior.
Interface fields are referenced through the `interface` symbol.

**Map Description**
A *static* unit has a [map description](map.md) defining a static address translation
function that is fixed at compile time.

**Translate Description**
A *configurable* unit has a [translate description](translate.md). This defines the
translation behavior of the unit.

**Map/Unmap/Protect**
A unit may define [map/unmap/protect functions](mapunmapprotect.md). These methods
provide constraints used by the synthesis step.


## Additional Unit Components

**Constants**
Units can have [constant definitions](constants.md). In contrast to the constants
defined at the top level, those constants are available within the scope of the unit.

**Methods**
Units can have [method definitions](methods.md) that provide a mechanism to provide
a commonly used computation over the state.


## Unit Parameters

A unit may be parameterized. This is required to define the state of the unit that may
be located at a specific address that is unknown at compile time. For example, a
page table may be allocated anywhere in memory subject to alignment constraints.

## Derivation (Inheritance)

A unit can be derived from another unit. This is similar to inheritance.
The deriving units can overwrite certain aspects, or fill in blanks in a
template provided by the derived unit.
