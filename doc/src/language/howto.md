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

It is important to identify all aspects that may define the translation behavior:
 - registers that enable/disable translations
 - registers that directly control the translation
 - registers holding pointers to in-memory data structures
 - in-memory data structures

**x86_64 MMU**

In this example, we can identify:
 - cr4 register that controls whether translation is enabled or not.
 - cr3 register that holds a pointer to an in-memory data structure
 - radix tree with four levels: PML4, PDPT, PDIR, PT as an in-memory data structure

## 2. Identify the Units

The next step involves identifying the [units](parser/units.md). Note, there may
be more than one way to represent a specific translation hardware in terms of a collection
of units.

The following a few steps to identify the units, given the state identified above

***1. one state type, one unit.***
For each state type (register or memory) define one unit. This results in one or two units.

***2. Split in-memory state***
For each distinct part of the in-memory state (e.g., table type) define a new unit.

***3. Separate "arrays of entries"***
Translation hardware may allow controlling several regions in the same fashion (e.g.,
a page table has a set of equal entries that control a portion of the translation).
This suggests expressing the entry as its own unit, and the table as a separate unit
that has collection of these entry units.

**x86_64 MMU**

Applying those steps we get the following:
 1. RegisterUnit for CR3/CR4 registers, and PageTableUnit for the radix tree.
 2. Split the radix tree into distinct components: PML4, PDPT, PDIR, PT
 3. Separate the entries. all in-memory tables are array of entries.

This yields the following units: PML4, PML4_Entry, PDPT, PDPT_Entry, PDIR, PDIR_Entry, PT, PT_Entry, x86MMU


## 3. Identify the Interface

For each unit, identify the interface software uses to interact with it.

**1. In-memory state => Memory Interface**
For in-memory states, select the memory interface for the unit.

**2. Memory-mapped registers => MMIO Interface**
For registers that are exposed to software through memory mapped registers, use a MMIO interface for
the unit. Identify the layout of the MMIO interface, and what happens when the register is read/
written.

**3. Specific registers => CPU Register Interface**
For registers that are exposed to software through distinct CPU registers, use a CPURegister
interface. Identify the layout of the CPU registers, and what happens when the register is read/
written.


**x86_64 MMU**
 - page tables: Memory Interface for all entries.
 - CPU registers: CR3 holding base and context identifier, CR4 to enable/disable translation


## 4. Formulate Translation Function and Constraints

The next step is to formulate the translation function for each unit and to define the
constraints.

**Translate:** There are two aspects to consider:
 1. When does it successfully translate. For each condition add a `requires` clause
 2. formulate how it translates.
```vrs
fn translate(va: addr, flags: int) -> addr
```

**Constraints** For each of the three functions `map/unmap/protect` think of the constraints
that need to be met. Minimum and Maximum supported values, alignments, ...

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
        entry [base, 0, 8] {
             0  0 present,
            // more fields omitted
            12 63 frame_addr
        };
    };
    // the interface has the same
    interface = Memory;

    // the translation semantics
    fn translate(va: addr, flags: int) -> addr
      requires state.entry.present; // present bit must be set
    {
        return (state.frame_addr << 12) + va;
    }
};

unit X86PageTable(base: addr) {
    // the table itself doesn't have state or interface

    // it has 512 entries expressed as a map
    staticmap = [ X86PageTableEntry(base + i * 8) for i in 0..512 ];

    // translate basically forwards the translation to the entry
    // this is for illustration purposes only, and is not required,
    // as it is derived from the staticmap description
    fn translate(va: addr, flags: int) -> addr {
        return staticmap[va / 4096].translate(va % 4096, flags)
    }
};
```