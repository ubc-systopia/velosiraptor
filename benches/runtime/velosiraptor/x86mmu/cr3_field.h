/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Field interface for `X86MMU::cr3`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X86MMU_CR3_FIELD_H_
#define X86MMU_CR3_FIELD_H_ 1


#include <stdint.h>

/// Defined constant for masking field `cr3`
/// @loc: examples/x86_64_pagetable.vrs:444:9
#define X86MMU_CR3__MASK (uint64_t)0xffffffffffffffff

/// Field Type `cr3`
/// @loc: examples/x86_64_pagetable.vrs:444:9
struct x86mmu_cr3 {
    uint64_t _val;
};

typedef struct x86mmu_cr3 x86mmu_cr3__t;

/// gets value cr3 in field
static inline uint64_t x86mmu_cr3__get_raw(x86mmu_cr3__t field) {
    return (field)._val;
}

/// sets value cr3 in field
static inline x86mmu_cr3__t x86mmu_cr3__set_raw(uint64_t val) {
    x86mmu_cr3__t field;
    (field)._val = (val & X86MMU_CR3__MASK);
    return field;
}

/// inserts value cr3.pcid [0..12] in field
/// @loc: examples/x86_64_pagetable.vrs:433:13
static inline x86mmu_cr3__t x86mmu_cr3_pcid__insert(x86mmu_cr3__t field, uint64_t val) {
    (field)._val = (field._val & 0xfffffffffffff000ULL) | (val & 0x0fff);
    return field;
}

/// extracts value cr3.pcid [0..12] in field
/// @loc: examples/x86_64_pagetable.vrs:433:13
static inline uint64_t x86mmu_cr3_pcid__extract(x86mmu_cr3__t field) {
    return (field._val & 0x0fff);
}

/// inserts value cr3.address [12..64] in field
/// @loc: examples/x86_64_pagetable.vrs:434:13
static inline x86mmu_cr3__t x86mmu_cr3_address__insert(x86mmu_cr3__t field, uint64_t val) {
    (field)._val = (field._val & 0x0000000000000fffULL) | ((val & 0x000fffffffffffffULL) << 12);
    return field;
}

/// extracts value cr3.address [12..64] in field
/// @loc: examples/x86_64_pagetable.vrs:434:13
static inline uint64_t x86mmu_cr3_address__extract(x86mmu_cr3__t field) {
    return ((field._val >> 12) & 0x000fffffffffffffULL);
}

#endif // X86MMU_CR3_FIELD_H_
