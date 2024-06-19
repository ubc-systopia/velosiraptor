/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Unit Definitions for `X8664PDirEntry`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDIRENTRY_UNIT_H_
#define X8664PDIRENTRY_UNIT_H_ 1


#include <stddef.h>

#include <assert.h>

#include "types.h"

#include "consts.h"

#include <myos.h>

#include "x8664pdirentrytable_unit.h"

#include "x8664pdirentrypage_unit.h"

//  --------------------------- Constants / Constructor -------------------------

/// Unit Type `X8664PDirEntry`
/// @loc: ../../examples/x86_64_pagetable.vrs:262:1
struct x8664pdirentry {
    uintptr_t base;
};

typedef struct x8664pdirentry x8664pdirentry__t;

static inline void x8664pdirentry_init(x8664pdirentry__t * unit, uint64_t base) {
    (unit)->base = base;
}

//  ----------------------------- Address Translation  --------------------------

//  ---------------------------- Map / Protect/ Unmap ---------------------------

static inline bool x8664pdirentry_is_valid(x8664pdirentry__t * unit) {
    x8664pdirentrytable__t v0;
    x8664pdirentrytable_init(&(v0), (unit)->base);
    x8664pdirentrypage__t v1;
    x8664pdirentrypage_init(&(v1), (unit)->base);
    return (x8664pdirentrytable_is_valid(&(v0)) || x8664pdirentrypage_is_valid(&(v1)));
}

static inline bool x8664pdirentry_is_table(x8664pdirentry__t * unit) {
    x8664pdirentrytable__t targetunit;
    x8664pdirentrytable_init(&(targetunit), (unit)->base);
    // Extracting the state values
    uint64_t state_entry_ps_val;
    state_entry_ps_val = x8664pdirentrytable_entry_ps__rd(&(targetunit));
    // Evaluate boolean expression on the state
    bool res;
    res = (state_entry_ps_val == 0x0);
    return res;
}

static inline bool x8664pdirentry_is_page(x8664pdirentry__t * unit) {
    x8664pdirentrypage__t targetunit;
    x8664pdirentrypage_init(&(targetunit), (unit)->base);
    // Extracting the state values
    uint64_t state_entry_ps_val;
    state_entry_ps_val = x8664pdirentrypage_entry_ps__rd(&(targetunit));
    // Evaluate boolean expression on the state
    bool res;
    res = (state_entry_ps_val == 0x1);
    return res;
}

//  ----------------------------- Allocate and free ----------------------------

// not a group root, cannot allocate

// not a group root, cannot allocate

//  --------------------------- Higher Order Functions --------------------------

static inline size_t x8664pdirentry_map_page(x8664pdirentry__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    // Variant: X8664PDirEntryPage mapping frame
    // TODO: check if there is already a valid mapping in there
    x8664pdirentrypage__t entry;
    x8664pdirentrypage_init(&(entry), (unit)->base);
    return x8664pdirentrypage_map(&(entry), va, sz, flgs, pa);
}

static inline size_t x8664pdirentry_map_table(x8664pdirentry__t * unit, vaddr_t va, size_t sz, flags_t flgs, x8664pagetable__t * pa) {
    // Variant: X8664PDirEntryTable mapping table
    // TODO: check if there is already a valid mapping in there
    x8664pdirentrytable__t entry;
    x8664pdirentrytable_init(&(entry), (unit)->base);
    return __x8664pdirentrytable_do_map(&(entry), va, sz, flgs, pa);
}

static inline size_t x8664pdirentry_map(x8664pdirentry__t * unit, vaddr_t va, size_t sz, flags_t flgs, paddr_t pa) {
    if ((((sz == 0x200000) && (va == 0x0)) && ((pa & 0x1fffff) == 0x0))) {
        // Variant: X8664PDirEntryPage mapping frame
        // TODO: check if there is already a valid mapping in there
        x8664pdirentrypage__t entry;
        x8664pdirentrypage_init(&(entry), (unit)->base);
        return x8664pdirentrypage_map(&(entry), va, sz, flgs, pa);
    } else  {
        // Variant: X8664PDirEntryTable mapping table
        // TODO: check if there is already a valid mapping in there
        x8664pdirentrytable__t entry;
        x8664pdirentrytable_init(&(entry), (unit)->base);
        return x8664pdirentrytable_map(&(entry), va, sz, flgs, pa);
    }
    return false;
}

static inline size_t x8664pdirentry_protect(x8664pdirentry__t * unit, vaddr_t va, size_t sz, flags_t flgs) {
    // Variant: X8664PDirEntryTable
    if (x8664pdirentry_is_table(unit)) {
        x8664pdirentrytable__t next;
        x8664pdirentrytable_init(&(next), (unit)->base);
        return x8664pdirentrytable_protect(&(next), va, sz, flgs);
    }
    // Variant: X8664PDirEntryPage
    if (x8664pdirentry_is_page(unit)) {
        x8664pdirentrypage__t next;
        x8664pdirentrypage_init(&(next), (unit)->base);
        return x8664pdirentrypage_protect(&(next), va, sz, flgs);
    }
    return false;
}

static inline size_t x8664pdirentry_unmap(x8664pdirentry__t * unit, vaddr_t va, size_t sz) {
    // Variant: X8664PDirEntryTable
    if (x8664pdirentry_is_table(unit)) {
        x8664pdirentrytable__t next;
        x8664pdirentrytable_init(&(next), (unit)->base);
        return x8664pdirentrytable_unmap(&(next), va, sz);
    }
    // Variant: X8664PDirEntryPage
    if (x8664pdirentry_is_page(unit)) {
        x8664pdirentrypage__t next;
        x8664pdirentrypage_init(&(next), (unit)->base);
        return x8664pdirentrypage_unmap(&(next), va, sz);
    }
    return false;
}

static inline bool x8664pdirentry_resolve(x8664pdirentry__t * unit, vaddr_t va, paddr_t * pa) {
    // Variant: X8664PDirEntryTable
    if (x8664pdirentry_is_table(unit)) {
        x8664pdirentrytable__t next;
        x8664pdirentrytable_init(&(next), (unit)->base);
        return x8664pdirentrytable_resolve(&(next), va, pa);
    }
    // Variant: X8664PDirEntryPage
    if (x8664pdirentry_is_page(unit)) {
        x8664pdirentrypage__t next;
        x8664pdirentrypage_init(&(next), (unit)->base);
        return x8664pdirentrypage_resolve(&(next), va, pa);
    }
    return false;
}

#endif // X8664PDIRENTRY_UNIT_H_
