/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Unit Definitions for `X8664PML4`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PML4_UNIT_H_
#define X8664PML4_UNIT_H_ 1


#include <stddef.h>

#include <assert.h>

#include <string.h>

#include "types.h"

#include "consts.h"

#include <myos.h>

#include "x8664pml4entry_unit.h"

//  --------------------------------- Constants ---------------------------------

// Defined unit constants

// The unit does not define any constants

//  -------------------------------- Constructor --------------------------------

/// Unit Type `X8664PML4`
/// @loc: ../../examples/x86_64_pagetable.vrs:395:1
struct x8664pml4 {
    uintptr_t base;
};

typedef struct x8664pml4 x8664pml4__t;

/// constructor of the unit type
static inline void x8664pml4_init(x8664pml4__t * unit, paddr_t base) {
    (unit)->base = base;
}

//  ----------------------------- Allocate and free ----------------------------

/// allocates memory to hold the in-memory state of the unit
static inline bool x8664pml4_alloc(x8664pml4__t * unit) {
    (unit)->base = memory_alloc(0x1000, 0x1000);
    if (((unit)->base == 0x0)) {
        return false;
    }
    return true;
}

/// frees memory that holds the in-memory state of the unit
static inline void x8664pml4_free(x8664pml4__t unit) {
    memory_free((unit).base, 0x1000);
}

//  ----------------------------- Accessing Children  --------------------------

// No set-child function needed as no environment spec available.

/// Gets the child pointer of the unit
static inline x8664pml4entry__t x8664pml4_get_child(x8664pml4__t * unit, vaddr_t va) {
    assert((va < 0x1000000000000));
    size_t idx;
    idx = (va >> 0x27);
    x8664pml4entry__t child_unit;
    x8664pml4entry_init(&(child_unit), ((idx * 0x8) + (unit)->base));
    return child_unit;
}

//  ---------------------------- Map / Protect/ Unmap ---------------------------

//  --------------------------- Higher Order Functions --------------------------

static inline size_t x8664pml4_map_entry(x8664pml4__t * unit, vaddr_t va, size_t sz, flags_t flgs, x8664pdpt__t * pa) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pml4entry__t child;
    child = x8664pml4_get_child(unit, va);
    // Recurse on child unit
    return __x8664pml4entry_do_map(&(child), (va & 0x7fffffffff), sz, flgs, pa);
}

static inline size_t x8664pml4_map(x8664pml4__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pml4entry__t child;
    child = x8664pml4_get_child(unit, va);
    // Recurse on child unit
    return x8664pml4entry_map(&(child), (va & 0x7fffffffff), sz, flgs, pa);
}

static inline size_t x8664pml4_protect(x8664pml4__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pml4entry__t child;
    child = x8664pml4_get_child(unit, va);
    // Recurse on child unit
    return x8664pml4entry_protect(&(child), (va & 0x7fffffffff), sz, flgs);
}

static inline size_t x8664pml4_unmap(x8664pml4__t * unit, vaddr_t va, size_t sz) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pml4entry__t child;
    child = x8664pml4_get_child(unit, va);
    // Recurse on child unit
    return x8664pml4entry_unmap(&(child), (va & 0x7fffffffff), sz);
}

static inline bool x8664pml4_resolve(x8664pml4__t * unit, vaddr_t va, paddr_t * pa) {
    // resolve directly
    // get the child unit
    x8664pml4entry__t child;
    child = x8664pml4_get_child(unit, va);
    // recurse on next unit
    return x8664pml4entry_resolve(&(child), (va & 0x7fffffffff), pa);
}

#endif // X8664PML4_UNIT_H_
