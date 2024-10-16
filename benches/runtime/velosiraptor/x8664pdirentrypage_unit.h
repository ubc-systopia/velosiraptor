/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Unit Definitions for `X8664PDirEntryPage`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDIRENTRYPAGE_UNIT_H_
#define X8664PDIRENTRYPAGE_UNIT_H_ 1


#include <stddef.h>

#include <assert.h>

#include <string.h>

#include <myos.h>

#include "x8664pdirentrypage_interface.h"

#include "consts.h"

#include "types.h"

//  --------------------------- Constants / Constructor -------------------------

// The unit does not define any constants

/// constructor of the unit type
static inline void x8664pdirentrypage_init(x8664pdirentrypage__t * unit, paddr_t base) {
    memset(unit, 0x0, sizeof(*(unit)));
    (unit)->base = base;
}

//  ----------------------------- Allocate and free ----------------------------

// not a group root, cannot allocate

// not a group root, cannot allocate

//  ----------------------------- Address Translation  --------------------------

/// Returns true if the mapping is valid
static inline bool x8664pdirentrypage_is_valid(x8664pdirentrypage__t * unit) {
    uint64_t state_entry_present_val;
    state_entry_present_val = x8664pdirentrypage_entry_present__rd(unit);
    return (state_entry_present_val == 0x1);
}

/// Returns true if the mapping is valid
static inline paddr_t x8664pdirentrypage_do_translate(x8664pdirentrypage__t * unit, vaddr_t va) {
    uint64_t state_entry_address_val;
    state_entry_address_val = x8664pdirentrypage_entry_address__rd(unit);
    uint64_t state_entry_ps_val;
    state_entry_ps_val = x8664pdirentrypage_entry_ps__rd(unit);
    // asserts for the requires clauses
    assert((state_entry_ps_val == 0x1));
    assert((va < 0x200000));
    assert(x8664pdirentrypage_is_valid(unit));
    return ((state_entry_address_val << 0x15) + va);
}

// No set-child function needed as no environment spec available.

//  ---------------------------- Map / Protect/ Unmap ---------------------------

/// Performs the synth fn map(va: vaddr, sz: size, flgs: flags, pa: paddr) -> ()
///   requires sz == 0x200000;
///   requires va == 0x0;
///   requires (pa & 0x1fffff) == 0x0; operation on the unit
static inline size_t __x8664pdirentrypage_do_map(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // requires sz == 0x200000
    if (!((sz == 0x200000))) {
        return 0x0;
    }
    // requires va == 0x0
    if (!((va == 0x0))) {
        return 0x0;
    }
    // requires (pa & 0x1fffff) == 0x0
    if (!(((pa & 0x1fffff) == 0x0))) {
        return 0x0;
    }
    // field variables
    x8664pdirentrypage_entry__t entry = x8664pdirentrypage_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdirentrypage_entry__set_raw(0x0);
    entry = x8664pdirentrypage_entry_address__insert(entry, ((pa >> 0x15) & 0x7ffffff));
    entry = x8664pdirentrypage_entry_ps__insert(entry, 0x1);
    entry = x8664pdirentrypage_entry_present__insert(entry, 0x1);
    entry = x8664pdirentrypage_entry_xd__insert(entry, !((flgs).executable));
    entry = x8664pdirentrypage_entry_us__insert(entry, (flgs).usermode);
    entry = x8664pdirentrypage_entry_pcd__insert(entry, (flgs).devicemem);
    entry = x8664pdirentrypage_entry_pwt__insert(entry, (flgs).devicemem);
    entry = x8664pdirentrypage_entry_rw__insert(entry, (flgs).writable);
    x8664pdirentrypage_entry__wr(unit, entry);
    return sz;
}

/// Performs the synth fn unmap(va: vaddr, sz: size) -> ()
///   requires sz == 0x200000;
///   requires va == 0x0; operation on the unit
static inline size_t __x8664pdirentrypage_do_unmap(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz) {
    // requires sz == 0x200000
    if (!((sz == 0x200000))) {
        return 0x0;
    }
    // requires va == 0x0
    if (!((va == 0x0))) {
        return 0x0;
    }
    // field variables
    x8664pdirentrypage_entry__t entry = x8664pdirentrypage_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdirentrypage_entry__set_raw(0x0);
    entry = x8664pdirentrypage_entry_present__insert(entry, 0x0);
    x8664pdirentrypage_entry__wr(unit, entry);
    return sz;
}

/// Performs the synth fn protect(va: vaddr, sz: size, flgs: flags) -> ()
///   requires true; operation on the unit
static inline size_t __x8664pdirentrypage_do_protect(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // field variables
    x8664pdirentrypage_entry__t entry = x8664pdirentrypage_entry__set_raw(0x0);
    // configuration sequence
    entry = x8664pdirentrypage_entry__rd(unit);
    entry = x8664pdirentrypage_entry_ps__insert(entry, 0x1);
    entry = x8664pdirentrypage_entry_xd__insert(entry, !((flgs).executable));
    entry = x8664pdirentrypage_entry_us__insert(entry, (flgs).usermode);
    entry = x8664pdirentrypage_entry_pcd__insert(entry, (flgs).devicemem);
    entry = x8664pdirentrypage_entry_pwt__insert(entry, (flgs).devicemem);
    entry = x8664pdirentrypage_entry_rw__insert(entry, (flgs).writable);
    x8664pdirentrypage_entry__wr(unit, entry);
    return sz;
}

//  --------------------------- Higher Order Functions --------------------------

/// Higher-order map function
static inline size_t x8664pdirentrypage_map(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // this is just calling the operation on the unit directy
    return __x8664pdirentrypage_do_map(unit, va, sz, flgs, pa);
}

/// Higher-order protect function
static inline size_t x8664pdirentrypage_protect(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // this is just calling the operation on the unit directy
    return __x8664pdirentrypage_do_protect(unit, va, sz, flgs);
}

/// Higher-order unmap function
static inline size_t x8664pdirentrypage_unmap(x8664pdirentrypage__t * unit, vaddr_t va, size_t sz) {
    // this is just calling the operation on the unit directy
    return __x8664pdirentrypage_do_unmap(unit, va, sz);
}

static inline bool x8664pdirentrypage_resolve(x8664pdirentrypage__t * unit, vaddr_t va, paddr_t * pa) {
    if (!(x8664pdirentrypage_is_valid(unit))) {
        return false;
    }
    *(pa) = x8664pdirentrypage_do_translate(unit, va);
    return true;
}

#endif // X8664PDIRENTRYPAGE_UNIT_H_
