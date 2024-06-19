/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Unit Definitions for `X8664PDPT`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDPT_UNIT_H_
#define X8664PDPT_UNIT_H_ 1


#include <stddef.h>

#include <assert.h>

#include <string.h>

#include "types.h"

#include "consts.h"

#include <myos.h>

#include "x8664pdptentry_unit.h"

//  --------------------------------- Constants ---------------------------------

// Defined unit constants

// The unit does not define any constants

//  -------------------------------- Constructor --------------------------------

/// Unit Type `X8664PDPT`
/// @loc: ../../examples/x86_64_pagetable.vrs:371:1
struct x8664pdpt {
    uintptr_t base;
};

typedef struct x8664pdpt x8664pdpt__t;

/// constructor of the unit type
static inline void x8664pdpt_init(x8664pdpt__t * unit, paddr_t base) {
    (unit)->base = base;
}

//  ----------------------------- Allocate and free ----------------------------

/// allocates memory to hold the in-memory state of the unit
static inline bool x8664pdpt_alloc(x8664pdpt__t * unit) {
    (unit)->base = memory_alloc(0x1000, 0x1000);
    if (((unit)->base == 0x0)) {
        return false;
    }
    return true;
}

/// frees memory that holds the in-memory state of the unit
static inline void x8664pdpt_free(x8664pdpt__t unit) {
    memory_free((unit).base, 0x1000);
}

//  ----------------------------- Accessing Children  --------------------------

// No set-child function needed as no environment spec available.

/// Gets the child pointer of the unit
static inline x8664pdptentry__t x8664pdpt_get_child(x8664pdpt__t * unit, vaddr_t va) {
    assert((va < 0x8000000000));
    size_t idx;
    idx = (va >> 0x1e);
    x8664pdptentry__t child_unit;
    x8664pdptentry_init(&(child_unit), ((idx * 0x8) + (unit)->base));
    return child_unit;
}

//  ---------------------------- Map / Protect/ Unmap ---------------------------

//  --------------------------- Higher Order Functions --------------------------

static inline size_t x8664pdpt_map_entrytable(x8664pdpt__t * unit, vaddr_t va, size_t sz, flags_t flgs, x8664pdir__t * pa) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // Recurse on child unit
    return x8664pdptentry_map_table(&(child), (va & 0x3fffffff), sz, flgs, pa);
}

static inline size_t x8664pdpt_map_entrypage(x8664pdpt__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // Recurse on child unit
    return x8664pdptentry_map_page(&(child), (va & 0x3fffffff), sz, flgs, pa);
}

static inline size_t x8664pdpt_map(x8664pdpt__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // Recurse on child unit
    return x8664pdptentry_map(&(child), (va & 0x3fffffff), sz, flgs, pa);
}

static inline size_t x8664pdpt_protect(x8664pdpt__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // Recurse on child unit
    return x8664pdptentry_protect(&(child), (va & 0x3fffffff), sz, flgs);
}

static inline size_t x8664pdpt_unmap(x8664pdpt__t * unit, vaddr_t va, size_t sz) {
    // Entry: Segment mapping a frame (direct access)
    // Get the child unit (i.e., the map entry)
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // Recurse on child unit
    return x8664pdptentry_unmap(&(child), (va & 0x3fffffff), sz);
}

static inline bool x8664pdpt_resolve(x8664pdpt__t * unit, vaddr_t va, paddr_t * pa) {
    // resolve directly
    // get the child unit
    x8664pdptentry__t child;
    child = x8664pdpt_get_child(unit, va);
    // recurse on next unit
    return x8664pdptentry_resolve(&(child), (va & 0x3fffffff), pa);
}

#endif // X8664PDPT_UNIT_H_
