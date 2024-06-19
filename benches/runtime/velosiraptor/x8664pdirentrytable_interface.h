/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Interface Definitions for `X8664PDirEntryTable`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDIRENTRYTABLE_INTERFACE_H_
#define X8664PDIRENTRYTABLE_INTERFACE_H_ 1


#include "types.h"

#include <os_mmio.h>

#include <os_registers.h>

#include <os_memory.h>

/// Unit Type `X8664PDirEntryTable`
/// @loc: ../../examples/x86_64_pagetable.vrs:184:1
struct x8664pdirentrytable {
    uintptr_t base;
};

typedef struct x8664pdirentrytable x8664pdirentrytable__t;

#include "x8664pdirentrytable/entry_field.h"

// Reading interface fields

/// reads the `entry` interface field
static inline x8664pdirentrytable_entry__t x8664pdirentrytable_entry__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__set_raw(os_memory_read_64(local_phys_to_mem((unit)->base), 0x0));
    return val;
}

/// reads the value `entry.present` from the interface
static inline uint8_t x8664pdirentrytable_entry_present__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_present__extract(val);
}

/// reads the value `entry.rw` from the interface
static inline uint8_t x8664pdirentrytable_entry_rw__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_rw__extract(val);
}

/// reads the value `entry.us` from the interface
static inline uint8_t x8664pdirentrytable_entry_us__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_us__extract(val);
}

/// reads the value `entry.pwt` from the interface
static inline uint8_t x8664pdirentrytable_entry_pwt__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_pwt__extract(val);
}

/// reads the value `entry.pcd` from the interface
static inline uint8_t x8664pdirentrytable_entry_pcd__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_pcd__extract(val);
}

/// reads the value `entry.a` from the interface
static inline uint8_t x8664pdirentrytable_entry_a__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_a__extract(val);
}

/// reads the value `entry.ignored0` from the interface
static inline uint8_t x8664pdirentrytable_entry_ignored0__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_ignored0__extract(val);
}

/// reads the value `entry.ps` from the interface
static inline uint8_t x8664pdirentrytable_entry_ps__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_ps__extract(val);
}

/// reads the value `entry.ignored1` from the interface
static inline uint8_t x8664pdirentrytable_entry_ignored1__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_ignored1__extract(val);
}

/// reads the value `entry.address` from the interface
static inline uint64_t x8664pdirentrytable_entry_address__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_address__extract(val);
}

/// reads the value `entry.res0` from the interface
static inline uint8_t x8664pdirentrytable_entry_res0__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_res0__extract(val);
}

/// reads the value `entry.ignored3` from the interface
static inline uint16_t x8664pdirentrytable_entry_ignored3__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_ignored3__extract(val);
}

/// reads the value `entry.xd` from the interface
static inline uint8_t x8664pdirentrytable_entry_xd__rd(x8664pdirentrytable__t * unit) {
    x8664pdirentrytable_entry__t val;
    val = x8664pdirentrytable_entry__rd(unit);
    return x8664pdirentrytable_entry_xd__extract(val);
}

// Writing interface fields

/// writes the `entry` interface field
static inline void x8664pdirentrytable_entry__wr(x8664pdirentrytable__t * unit, x8664pdirentrytable_entry__t val) {
    os_memory_write_64(local_phys_to_mem((unit)->base), 0x0, x8664pdirentrytable_entry__get_raw(val));
}

/// writes the value `entry.present` from the interface
static inline void x8664pdirentrytable_entry_present__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_present__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.rw` from the interface
static inline void x8664pdirentrytable_entry_rw__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_rw__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.us` from the interface
static inline void x8664pdirentrytable_entry_us__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_us__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.pwt` from the interface
static inline void x8664pdirentrytable_entry_pwt__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_pwt__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.pcd` from the interface
static inline void x8664pdirentrytable_entry_pcd__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_pcd__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.a` from the interface
static inline void x8664pdirentrytable_entry_a__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_a__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.ignored0` from the interface
static inline void x8664pdirentrytable_entry_ignored0__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_ignored0__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.ps` from the interface
static inline void x8664pdirentrytable_entry_ps__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_ps__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.ignored1` from the interface
static inline void x8664pdirentrytable_entry_ignored1__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_ignored1__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.address` from the interface
static inline void x8664pdirentrytable_entry_address__wr(x8664pdirentrytable__t * unit, uint64_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_address__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.res0` from the interface
static inline void x8664pdirentrytable_entry_res0__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_res0__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.ignored3` from the interface
static inline void x8664pdirentrytable_entry_ignored3__wr(x8664pdirentrytable__t * unit, uint16_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_ignored3__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

/// writes the value `entry.xd` from the interface
static inline void x8664pdirentrytable_entry_xd__wr(x8664pdirentrytable__t * unit, uint8_t val) {
    x8664pdirentrytable_entry__t field;
    field = x8664pdirentrytable_entry__rd(unit);
    field = x8664pdirentrytable_entry_xd__insert(field, val);
    x8664pdirentrytable_entry__wr(unit, field);
}

#endif // X8664PDIRENTRYTABLE_INTERFACE_H_
