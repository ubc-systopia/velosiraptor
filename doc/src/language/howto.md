# HowTo: Specifying Translation Hardware

The goal of the specification is to faithfully capture the translation semantics of
a real (or imaginary) piece of translation hardware such as an MMU, segment registers, etc.

This section outlines a general strategy to specify the translation hardware as
a collection of [units](parser/units.md).

As a running example, consider an x86_64 MMU.

## 1. Identify the State

The initial question to ask is what determines how the hardware actually translates memory
addresses. In other words, what is the state that defines the translation function?
For example, this may be some specific registers, or an in-memory data structure
such as the page table. This step also identifies the layout of the state (the meaning of bits),
and how the translation is defined with respect to those bits.

**x86_64 MMU**
 - radix tree with four levels: PML4, PDPT, PDIR, PT
 - CPU registers: CR3, CR4
 - entry: base address and flags, only translates if the present bit is set.


## 2. Identify the Units

The next step involves identifying the [units](parser/units.md). Note, there may
be more than one way to represent a specific translation hardware in terms of a collection
of units.

The following a few *rules of thumb*.

***Rule 1: one state, one unit.***
Translation hardware may make use of different in-memory data structures, or registers (e.g.,
a page directory table is different from a page table). Thus, to represent a four-level
page table implies 5 different units (one for each level of the page table, plus one to
express the processor registers).

***Rule 2: One unit for each array entry***
Translation hardware may allow controlling several regions in the same fashion (e.g.,
a page table has a set of equal entries that control a portion of the translation).
This suggests expressing the entry as its own unit, and the table as a separate unit
that has collection of these entry units.

**x86_64 MMU**

Applying those rules to the identified state yields nine different units:

 - Units: PML4, PML4_Entry, PDPT, PDPT_Entry, PDIR, PDIR_Entry, PT, PT_Entry, x86MMU


## 3. Identify the Interface

System software interacts with the translation hardware in a certain way. This may be through
a register interface, or by writing to a specific memory location. This step identifies
the interface used with its fields and the meaning its contents.

**x86_64 MMU**
 - page tables: load-store interface to memory, one field (the entry) with present bit, base ...
 - CPU registers: CR3 holding base and context identifier, CR4 to enable/disable translation

## 4. Putting it Together

The previous steps identified:

 1. the units with their state
 2. the interface software uses to interact with the units.
 3. how hardware translates with respect to the current state.

Using this information, one can now write down the specification of the translation
hardware.

```vrs
unit X86PageTableEntry(base: addr) {
    state = Memory(base: addr) {
        entry [base, 0, 0] {
             0  0 present,
            // more fields omitted
            12 63 base
        };
    };
    // the interface has the same
    interface = Memory(base: addr);

    // the translation semantics
    fn translate(va: addr, flags: int) -> addr
      requires state.entry.present; // present bit must be set
    {
        return state.base << 12 + va;
    }
}

unit X86PageTable(base: addr) {
    // the table itself doesn't have state or interface

    // it has 512 entries expressed as a map
    map = [ X86PageTableEntry(base + i * 8) for i in 0..512 ];

    // translate basically forwards the translation to the entry
    fn translate(va: addr, flags: int) -> addr {
        return map[va / 4096].translate(va % 4096, flags)
    }
}
```