/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Field interface for `X8664PML4Entry::entry`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X8664PML4ENTRY_ENTRY_FIELD_H_
#define X8664PML4ENTRY_ENTRY_FIELD_H_ 1


#include <stdint.h>

/// Defined constant for masking field `entry`
/// @loc: examples/x86_64_pagetable.vrs:73:9
#define X8664PML4ENTRY_ENTRY__MASK (uint64_t)0xffffffffffffffff

/// Field Type `entry`
/// @loc: examples/x86_64_pagetable.vrs:73:9
struct x8664pml4entry_entry {
    uint64_t _val;
};

typedef struct x8664pml4entry_entry x8664pml4entry_entry__t;

/// gets value entry in field
static inline uint64_t x8664pml4entry_entry__get_raw(x8664pml4entry_entry__t field) {
    return (field)._val;
}

/// sets value entry in field
static inline x8664pml4entry_entry__t x8664pml4entry_entry__set_raw(uint64_t val) {
    x8664pml4entry_entry__t field;
    (field)._val = (val & X8664PML4ENTRY_ENTRY__MASK);
    return field;
}

/// inserts value entry.present [0..1] in field
/// @loc: examples/x86_64_pagetable.vrs:56:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_present__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffeULL) | (val & 0x01);
    return field;
}

/// extracts value entry.present [0..1] in field
/// @loc: examples/x86_64_pagetable.vrs:56:13
static inline uint64_t x8664pml4entry_entry_present__extract(x8664pml4entry_entry__t field) {
    return (field._val & 0x01);
}

/// inserts value entry.rw [1..2] in field
/// @loc: examples/x86_64_pagetable.vrs:57:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_rw__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffdULL) | ((val & 0x01) << 1);
    return field;
}

/// extracts value entry.rw [1..2] in field
/// @loc: examples/x86_64_pagetable.vrs:57:13
static inline uint64_t x8664pml4entry_entry_rw__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 1) & 0x01);
}

/// inserts value entry.us [2..3] in field
/// @loc: examples/x86_64_pagetable.vrs:58:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_us__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffffbULL) | ((val & 0x01) << 2);
    return field;
}

/// extracts value entry.us [2..3] in field
/// @loc: examples/x86_64_pagetable.vrs:58:13
static inline uint64_t x8664pml4entry_entry_us__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 2) & 0x01);
}

/// inserts value entry.pwt [3..4] in field
/// @loc: examples/x86_64_pagetable.vrs:59:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_pwt__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffffff7ULL) | ((val & 0x01) << 3);
    return field;
}

/// extracts value entry.pwt [3..4] in field
/// @loc: examples/x86_64_pagetable.vrs:59:13
static inline uint64_t x8664pml4entry_entry_pwt__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 3) & 0x01);
}

/// inserts value entry.pcd [4..5] in field
/// @loc: examples/x86_64_pagetable.vrs:60:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_pcd__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffefULL) | ((val & 0x01) << 4);
    return field;
}

/// extracts value entry.pcd [4..5] in field
/// @loc: examples/x86_64_pagetable.vrs:60:13
static inline uint64_t x8664pml4entry_entry_pcd__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 4) & 0x01);
}

/// inserts value entry.a [5..6] in field
/// @loc: examples/x86_64_pagetable.vrs:61:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_a__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffdfULL) | ((val & 0x01) << 5);
    return field;
}

/// extracts value entry.a [5..6] in field
/// @loc: examples/x86_64_pagetable.vrs:61:13
static inline uint64_t x8664pml4entry_entry_a__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 5) & 0x01);
}

/// inserts value entry.ignored0 [6..7] in field
/// @loc: examples/x86_64_pagetable.vrs:62:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_ignored0__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffffbfULL) | ((val & 0x01) << 6);
    return field;
}

/// extracts value entry.ignored0 [6..7] in field
/// @loc: examples/x86_64_pagetable.vrs:62:13
static inline uint64_t x8664pml4entry_entry_ignored0__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 6) & 0x01);
}

/// inserts value entry.ps [7..8] in field
/// @loc: examples/x86_64_pagetable.vrs:63:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_ps__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffffffffffffff7fULL) | ((val & 0x01) << 7);
    return field;
}

/// extracts value entry.ps [7..8] in field
/// @loc: examples/x86_64_pagetable.vrs:63:13
static inline uint64_t x8664pml4entry_entry_ps__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 7) & 0x01);
}

/// inserts value entry.ignored1 [8..12] in field
/// @loc: examples/x86_64_pagetable.vrs:64:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_ignored1__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffff0ffULL) | ((val & 0x0f) << 8);
    return field;
}

/// extracts value entry.ignored1 [8..12] in field
/// @loc: examples/x86_64_pagetable.vrs:64:13
static inline uint64_t x8664pml4entry_entry_ignored1__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 8) & 0x0f);
}

/// inserts value entry.address [12..48] in field
/// @loc: examples/x86_64_pagetable.vrs:65:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_address__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xffff000000000fffULL) | ((val & 0x0000000fffffffffULL) << 12);
    return field;
}

/// extracts value entry.address [12..48] in field
/// @loc: examples/x86_64_pagetable.vrs:65:13
static inline uint64_t x8664pml4entry_entry_address__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 12) & 0x0000000fffffffffULL);
}

/// inserts value entry.res0 [48..52] in field
/// @loc: examples/x86_64_pagetable.vrs:66:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_res0__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0xfff0ffffffffffffULL) | ((val & 0x0f) << 48);
    return field;
}

/// extracts value entry.res0 [48..52] in field
/// @loc: examples/x86_64_pagetable.vrs:66:13
static inline uint64_t x8664pml4entry_entry_res0__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 48) & 0x0f);
}

/// inserts value entry.ignored3 [52..63] in field
/// @loc: examples/x86_64_pagetable.vrs:67:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_ignored3__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0x800fffffffffffffULL) | ((val & 0x07ff) << 52);
    return field;
}

/// extracts value entry.ignored3 [52..63] in field
/// @loc: examples/x86_64_pagetable.vrs:67:13
static inline uint64_t x8664pml4entry_entry_ignored3__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 52) & 0x07ff);
}

/// inserts value entry.xd [63..64] in field
/// @loc: examples/x86_64_pagetable.vrs:68:13
static inline x8664pml4entry_entry__t x8664pml4entry_entry_xd__insert(x8664pml4entry_entry__t field, uint64_t val) {
    (field)._val = (field._val & 0x7fffffffffffffffULL) | ((val & 0x01) << 63);
    return field;
}

/// extracts value entry.xd [63..64] in field
/// @loc: examples/x86_64_pagetable.vrs:68:13
static inline uint64_t x8664pml4entry_entry_xd__extract(x8664pml4entry_entry__t field) {
    return ((field._val >> 63) & 0x01);
}

#endif // X8664PML4ENTRY_ENTRY_FIELD_H_
