/// 2022 Systopia Lab, Computer Science, University of British Columbia. All rights reserved.


// Field interface for `X86MMU::cr4`

// THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER



#ifndef X86MMU_CR4_FIELD_H_
#define X86MMU_CR4_FIELD_H_ 1


#include <stdint.h>

/// Defined constant for masking field `cr4`
/// @loc: examples/x86_64_pagetable.vrs:445:9
#define X86MMU_CR4__MASK (uint32_t)0x80000000

/// Field Type `cr4`
/// @loc: examples/x86_64_pagetable.vrs:445:9
struct x86mmu_cr4 {
    uint32_t _val;
};

typedef struct x86mmu_cr4 x86mmu_cr4__t;

/// gets value cr4 in field
static inline uint32_t x86mmu_cr4__get_raw(x86mmu_cr4__t field) {
    return (field)._val;
}

/// sets value cr4 in field
static inline x86mmu_cr4__t x86mmu_cr4__set_raw(uint32_t val) {
    x86mmu_cr4__t field;
    (field)._val = (val & X86MMU_CR4__MASK);
    return field;
}

/// inserts value cr4.enabled [31..32] in field
/// @loc: examples/x86_64_pagetable.vrs:438:13
static inline x86mmu_cr4__t x86mmu_cr4_enabled__insert(x86mmu_cr4__t field, uint32_t val) {
    (field)._val = (field._val & 0x7fffffffU) | ((val & 0x01) << 31);
    return field;
}

/// extracts value cr4.enabled [31..32] in field
/// @loc: examples/x86_64_pagetable.vrs:438:13
static inline uint32_t x86mmu_cr4_enabled__extract(x86mmu_cr4__t field) {
    return ((field._val >> 31) & 0x01);
}

#endif // X86MMU_CR4_FIELD_H_
