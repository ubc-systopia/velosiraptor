/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Unit Definitions for `X8664PDPTEntryTable`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDPTENTRYTABLE_UNIT_H_
#define X8664PDPTENTRYTABLE_UNIT_H_ 1


#include <stddef.h>

#include <assert.h>

#include <string.h>

#include <myos.h>

#include "x8664pdir_unit.h"

#include "x8664pdptentrytable_interface.h"

#include "consts.h"

#include "types.h"

//  --------------------------- Constants / Constructor -------------------------

// The unit does not define any constants

/// constructor of the unit type
static inline void x8664pdptentrytable_init(x8664pdptentrytable__t * unit, paddr_t base) {
    memset(unit, 0x0, sizeof(*(unit)));
    (unit)->base = base;
}

//  ----------------------------- Allocate and free ----------------------------

// not a group root, cannot allocate

// not a group root, cannot allocate

//  ----------------------------- Address Translation  --------------------------

/// Returns true if the mapping is valid
static inline bool x8664pdptentrytable_is_valid(x8664pdptentrytable__t * unit) {
    uint64_t state_entry_present_val;
    state_entry_present_val = x8664pdptentrytable_entry_present__rd(unit);
    return (state_entry_present_val == 0x1);
}

/// Returns true if the mapping is valid
static inline paddr_t x8664pdptentrytable_do_translate(x8664pdptentrytable__t * unit, vaddr_t va) {
    uint64_t state_entry_ps_val;
    state_entry_ps_val = x8664pdptentrytable_entry_ps__rd(unit);
    uint64_t state_entry_address_val;
    state_entry_address_val = x8664pdptentrytable_entry_address__rd(unit);
    // asserts for the requires clauses
    assert((state_entry_ps_val == 0x0));
    assert(x8664pdptentrytable_is_valid(unit));
    return (state_entry_address_val << 0xc);
}

// No set-child function needed as no environment spec available.

/// Gets the child pointer of the unit
static inline x8664pdir__t x8664pdptentrytable_get_child(x8664pdptentrytable__t * unit, vaddr_t va) {
    assert(x8664pdptentrytable_is_valid(unit));
    // get the address of the next table by calling translate
    paddr_t next_base;
    next_base = x8664pdptentrytable_do_translate(unit, 0x0);
    // construct the new unit
    x8664pdir__t next_unit;
    x8664pdir_init(&(next_unit), next_base);
    return next_unit;
}

//  ---------------------------- Map / Protect/ Unmap ---------------------------

/// Performs the synth fn map(va: vaddr, sz: size, flgs: flags, pa: X8664PDir) -> ()
///   requires (va + sz) <= 0x40000000;
///   requires 0x0 <= va;
///   requires (va & 0xfff) == 0x0;
///   requires (pa & 0xfff) == 0x0; operation on the unit
static inline size_t __x8664pdptentrytable_do_map(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz, flags_t flgs, x8664pdir__t * pa) {
    // requires (va + sz) <= 0x40000000
    if (!(((va + sz) <= 0x40000000))) {
        return 0x0;
    }
    // requires 0x0 <= va
    if (!((0x0 <= va))) {
        return 0x0;
    }
    // requires (va & 0xfff) == 0x0
    if (!(((va & 0xfff) == 0x0))) {
        return 0x0;
    }
    // requires (pa & 0xfff) == 0x0
    if (!(((0x0 & 0xfff) == 0x0))) {
        return 0x0;
    }
    // field variables
    x8664pdptentrytable_entry__t entry = x8664pdptentrytable_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdptentrytable_entry__rd(unit);
    entry = x8664pdptentrytable_entry_address__insert(entry, (((pa)->base >> 0xc) & 0x80fffffffff));
    entry = x8664pdptentrytable_entry_ps__insert(entry, 0x0);
    entry = x8664pdptentrytable_entry_present__insert(entry, 0x1);
    entry = x8664pdptentrytable_entry_res0__insert(entry, 0x0);
    entry = x8664pdptentrytable_entry_pcd__insert(entry, 0x0);
    entry = x8664pdptentrytable_entry_pwt__insert(entry, 0x0);
    entry = x8664pdptentrytable_entry_us__insert(entry, 0x1);
    entry = x8664pdptentrytable_entry_rw__insert(entry, 0x1);
    x8664pdptentrytable_entry__wr(unit, entry);
    return sz;
}

/// Performs the synth fn unmap(va: vaddr, sz: size) -> ()
///   requires (va + sz) <= 0x40000000;
///   requires 0x0 <= va;
///   requires (va & 0xfff) == 0x0; operation on the unit
static inline size_t __x8664pdptentrytable_do_unmap(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz) {
    // requires (va + sz) <= 0x40000000
    if (!(((va + sz) <= 0x40000000))) {
        return 0x0;
    }
    // requires 0x0 <= va
    if (!((0x0 <= va))) {
        return 0x0;
    }
    // requires (va & 0xfff) == 0x0
    if (!(((va & 0xfff) == 0x0))) {
        return 0x0;
    }
    // field variables
    x8664pdptentrytable_entry__t entry = x8664pdptentrytable_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdptentrytable_entry__set_raw(0x0);
    entry = x8664pdptentrytable_entry_present__insert(entry, 0x0);
    x8664pdptentrytable_entry__wr(unit, entry);
    return sz;
}

/// Performs the synth fn protect(va: vaddr, sz: size, flgs: flags) -> ()
///   requires (va + sz) <= 0x40000000;
///   requires 0x0 <= va;
///   requires (va & 0xfff) == 0x0; operation on the unit
static inline size_t __x8664pdptentrytable_do_protect(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // requires (va + sz) <= 0x40000000
    if (!(((va + sz) <= 0x40000000))) {
        return 0x0;
    }
    // requires 0x0 <= va
    if (!((0x0 <= va))) {
        return 0x0;
    }
    // requires (va & 0xfff) == 0x0
    if (!(((va & 0xfff) == 0x0))) {
        return 0x0;
    }
    // field variables
    x8664pdptentrytable_entry__t entry = x8664pdptentrytable_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdptentrytable_entry__rd(unit);
    entry = x8664pdptentrytable_entry_ps__insert(entry, 0x0);
    x8664pdptentrytable_entry__wr(unit, entry);
    return sz;
}

//  --------------------------- Higher Order Functions --------------------------

/// Higher-order map function
static inline size_t x8664pdptentrytable_map(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    x8664pdir__t next_unit;
    if (!(x8664pdptentrytable_is_valid(unit))) {
        // Allocate the next-level structure
        x8664pdir_alloc(&(next_unit));
        // TODO: Check whether allocation has succeeded!
        __x8664pdptentrytable_do_map(unit, 0x0, 0x40000000, DEFAULT_FLAGS, &(next_unit));
    } else  {
        next_unit = x8664pdptentrytable_get_child(unit, 0x0);
    }
    return x8664pdir_map(&(next_unit), va, sz, flgs, pa);
}

/// Higher-order protect function
static inline size_t x8664pdptentrytable_protect(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    x8664pdir__t next_unit;
    if (!(x8664pdptentrytable_is_valid(unit))) {
        return 0x0;
    }
    next_unit = x8664pdptentrytable_get_child(unit, 0x0);
    return x8664pdir_protect(&(next_unit), va, sz, flgs);
}

/// Higher-order unmap function
static inline size_t x8664pdptentrytable_unmap(x8664pdptentrytable__t * unit, vaddr_t va, size_t sz) {
    x8664pdir__t next_unit;
    if (!(x8664pdptentrytable_is_valid(unit))) {
        return 0x0;
    }
    next_unit = x8664pdptentrytable_get_child(unit, 0x0);
    return x8664pdir_unmap(&(next_unit), va, sz);
}

static inline bool x8664pdptentrytable_resolve(x8664pdptentrytable__t * unit, vaddr_t va, paddr_t * pa) {
    if (!(x8664pdptentrytable_is_valid(unit))) {
        return false;
    }
    x8664pdir__t next_unit;
    next_unit = x8664pdptentrytable_get_child(unit, 0x0);
    return x8664pdptentrytable_resolve(unit, va, pa);
}

#endif // X8664PDPTENTRYTABLE_UNIT_H_
