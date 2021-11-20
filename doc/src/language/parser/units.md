# Units

The unit is the core part of the specification. It combines the [state](state.md), the
[interface](interface.md) and [translation semantics](translate.md) to build a model
of the translation hardware unit.

Note, a complete translation scheme (e.g., an x86 memory management unit) is expressed as a
*collection* of units each of which modeling a specific aspect of it (e.g, a page table entry
at a specific level). The full specification is a *composition* of these units (e.g.,
a page table is a composition of 512 page table entries).

```
                +-----------------------+
  input addr    |                       |  output addr
 -------------> | translate(input addr) | ------------->
                |                       |
                +-----------------------+
                          unit
```

Conceptually, a unit *translates* an input address to an output address -- analogous (but not limited)
to a virtual to physical address translation. There are *two* distinct translation behaviors:

 1. The **static map** defines a *fixed* translation function known at compile time.
 2. The **configurable segment** defines a configurable translation function that depends
    on the runtime *state*.

In the page table example, the page table as a whole is a fixed mapping of an input address
onto one of the 512 entries, and in turn each entry is a configurable unit defining the
translation of the page.



## Grammar

```
UNIT :=
```

## Example

```vrs
unit Foo()
```



The unit has the following components:

 - a [state description](state.md)
