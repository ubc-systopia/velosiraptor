/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Field interface for `X8664PDPTEntryPage::entry`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PDPTENTRYPAGE_ENTRY_FIELD_H_
#define X8664PDPTENTRYPAGE_ENTRY_FIELD_H_ 1


#include <stdint.h>

/// Defined constant for masking field `entry`
/// @loc: examples/x86_64_pagetable.vrs:329:9
#define X8664PDPTENTRYPAGE_ENTRY__MASK (uint64_t)0xffffffffffffffff

/// Field Type `entry`
/// @loc: examples/x86_64_pagetable.vrs:329:9
struct x8664pdptentrypage_entry {
    uint64_t _val;
};

typedef struct x8664pdptentrypage_entry x8664pdptentrypage_entry__t;

/// gets value entry in field
static inline uint64_t x8664pdptentrypage_entry__get_raw(x8664pdptentrypage_entry__t field) {
    return (field)._val;
}

/// sets value entry in field
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry__set_raw(uint64_t val) {
    x8664pdptentrypage_entry__t field;
    (field)._val = (val & X8664PDPTENTRYPAGE_ENTRY__MASK);
    return field;
}

/// inserts value entry.present [0..1] in field
/// @loc: examples/x86_64_pagetable.vrs:308:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_present__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffeULL) | (val & 0x01);
    return field;
}

/// extracts value entry.present [0..1] in field
/// @loc: examples/x86_64_pagetable.vrs:308:13
static inline uint64_t x8664pdptentrypage_entry_present__extract(x8664pdptentrypage_entry__t field) {
    return (field._val & 0x01);
}

/// inserts value entry.rw [1..2] in field
/// @loc: examples/x86_64_pagetable.vrs:309:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_rw__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffdULL) | ((val & 0x01) << 1);
    return field;
}

/// extracts value entry.rw [1..2] in field
/// @loc: examples/x86_64_pagetable.vrs:309:13
static inline uint64_t x8664pdptentrypage_entry_rw__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 1) & 0x01);
}

/// inserts value entry.us [2..3] in field
/// @loc: examples/x86_64_pagetable.vrs:310:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_us__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffbULL) | ((val & 0x01) << 2);
    return field;
}

/// extracts value entry.us [2..3] in field
/// @loc: examples/x86_64_pagetable.vrs:310:13
static inline uint64_t x8664pdptentrypage_entry_us__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 2) & 0x01);
}

/// inserts value entry.pwt [3..4] in field
/// @loc: examples/x86_64_pagetable.vrs:311:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_pwt__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffff7ULL) | ((val & 0x01) << 3);
    return field;
}

/// extracts value entry.pwt [3..4] in field
/// @loc: examples/x86_64_pagetable.vrs:311:13
static inline uint64_t x8664pdptentrypage_entry_pwt__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 3) & 0x01);
}

/// inserts value entry.pcd [4..5] in field
/// @loc: examples/x86_64_pagetable.vrs:312:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_pcd__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffefULL) | ((val & 0x01) << 4);
    return field;
}

/// extracts value entry.pcd [4..5] in field
/// @loc: examples/x86_64_pagetable.vrs:312:13
static inline uint64_t x8664pdptentrypage_entry_pcd__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 4) & 0x01);
}

/// inserts value entry.a [5..6] in field
/// @loc: examples/x86_64_pagetable.vrs:313:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_a__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffdfULL) | ((val & 0x01) << 5);
    return field;
}

/// extracts value entry.a [5..6] in field
/// @loc: examples/x86_64_pagetable.vrs:313:13
static inline uint64_t x8664pdptentrypage_entry_a__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 5) & 0x01);
}

/// inserts value entry.d [6..7] in field
/// @loc: examples/x86_64_pagetable.vrs:314:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_d__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffbfULL) | ((val & 0x01) << 6);
    return field;
}

/// extracts value entry.d [6..7] in field
/// @loc: examples/x86_64_pagetable.vrs:314:13
static inline uint64_t x8664pdptentrypage_entry_d__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 6) & 0x01);
}

/// inserts value entry.ps [7..8] in field
/// @loc: examples/x86_64_pagetable.vrs:315:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_ps__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffff7fULL) | ((val & 0x01) << 7);
    return field;
}

/// extracts value entry.ps [7..8] in field
/// @loc: examples/x86_64_pagetable.vrs:315:13
static inline uint64_t x8664pdptentrypage_entry_ps__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 7) & 0x01);
}

/// inserts value entry.g [8..9] in field
/// @loc: examples/x86_64_pagetable.vrs:316:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_g__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffeffULL) | ((val & 0x01) << 8);
    return field;
}

/// extracts value entry.g [8..9] in field
/// @loc: examples/x86_64_pagetable.vrs:316:13
static inline uint64_t x8664pdptentrypage_entry_g__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 8) & 0x01);
}

/// inserts value entry.ign_0 [9..12] in field
/// @loc: examples/x86_64_pagetable.vrs:317:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_ign_0__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffff1ffULL) | ((val & 0x07) << 9);
    return field;
}

/// extracts value entry.ign_0 [9..12] in field
/// @loc: examples/x86_64_pagetable.vrs:317:13
static inline uint64_t x8664pdptentrypage_entry_ign_0__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 9) & 0x07);
}

/// inserts value entry.pat [12..13] in field
/// @loc: examples/x86_64_pagetable.vrs:318:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_pat__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffefffULL) | ((val & 0x01) << 12);
    return field;
}

/// extracts value entry.pat [12..13] in field
/// @loc: examples/x86_64_pagetable.vrs:318:13
static inline uint64_t x8664pdptentrypage_entry_pat__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 12) & 0x01);
}

/// inserts value entry.res0_0 [13..30] in field
/// @loc: examples/x86_64_pagetable.vrs:319:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_res0_0__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffc0001fffULL) | ((val & 0x0001ffffU) << 13);
    return field;
}

/// extracts value entry.res0_0 [13..30] in field
/// @loc: examples/x86_64_pagetable.vrs:319:13
static inline uint64_t x8664pdptentrypage_entry_res0_0__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 13) & 0x0001ffffU);
}

/// inserts value entry.address [30..48] in field
/// @loc: examples/x86_64_pagetable.vrs:320:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_address__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffff00003fffffffULL) | ((val & 0x0003ffffU) << 30);
    return field;
}

/// extracts value entry.address [30..48] in field
/// @loc: examples/x86_64_pagetable.vrs:320:13
static inline uint64_t x8664pdptentrypage_entry_address__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 30) & 0x0003ffffU);
}

/// inserts value entry.res0_1 [48..52] in field
/// @loc: examples/x86_64_pagetable.vrs:321:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_res0_1__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfff0ffffffffffffULL) | ((val & 0x0f) << 48);
    return field;
}

/// extracts value entry.res0_1 [48..52] in field
/// @loc: examples/x86_64_pagetable.vrs:321:13
static inline uint64_t x8664pdptentrypage_entry_res0_1__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 48) & 0x0f);
}

/// inserts value entry.ign_1 [52..59] in field
/// @loc: examples/x86_64_pagetable.vrs:322:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_ign_1__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xf80fffffffffffffULL) | ((val & 0x7f) << 52);
    return field;
}

/// extracts value entry.ign_1 [52..59] in field
/// @loc: examples/x86_64_pagetable.vrs:322:13
static inline uint64_t x8664pdptentrypage_entry_ign_1__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 52) & 0x7f);
}

/// inserts value entry.pkey [59..63] in field
/// @loc: examples/x86_64_pagetable.vrs:323:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_pkey__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0x87ffffffffffffffULL) | ((val & 0x0f) << 59);
    return field;
}

/// extracts value entry.pkey [59..63] in field
/// @loc: examples/x86_64_pagetable.vrs:323:13
static inline uint64_t x8664pdptentrypage_entry_pkey__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 59) & 0x0f);
}

/// inserts value entry.xd [63..64] in field
/// @loc: examples/x86_64_pagetable.vrs:324:13
static inline x8664pdptentrypage_entry__t x8664pdptentrypage_entry_xd__insert(x8664pdptentrypage_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0x7fffffffffffffffULL) | ((val & 0x01) << 63);
    return field;
}

/// extracts value entry.xd [63..64] in field
/// @loc: examples/x86_64_pagetable.vrs:324:13
static inline uint64_t x8664pdptentrypage_entry_xd__extract(x8664pdptentrypage_entry__t field) {
    return ((field._val >> 63) & 0x01);
}

#endif // X8664PDPTENTRYPAGE_ENTRY_FIELD_H_
