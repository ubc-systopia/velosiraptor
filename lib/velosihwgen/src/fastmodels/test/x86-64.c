#include <vrs_test.h>

typedef unsigned long int word;
typedef word *addr;

#ifndef MSG
#define MSG(format, ...) printf("[ARMv8]: " format, ##__VA_ARGS__)
#endif

#define CONTROL_BASE 0x100000000UL
/*             up to 0x13fffffff */
#define TRANSLATED_BASE 0x0C0000000UL
/*                up to  0xffffffff */

/* Helpers. Call with address in range 0 ... 0x3fffffff */
word read_paddr(volatile void *pa) {
    volatile addr pa2 = pa + CONTROL_BASE;
    MSG("Reading phys addr 0x%p (control addr 0x%p) ", pa, pa2);
    word data = *pa2;
    printf("value: 0x%lx\n", data);
    return data;
}

void write_paddr(volatile void *pa, word data) {
    volatile addr pa2 = pa + CONTROL_BASE;
    MSG("Writing phys addr 0x%p (control addr 0x%p): value 0x%lx\n", pa, pa2,
        data);
    /* addr huh = 0x100000000; */
    /* *huh = data; */
    /* MSG("TEST: %p, %p\n", pa2, huh); */
    *pa2 = data;
}

word read_vaddr(volatile void *va) {
    volatile addr va2 = va + TRANSLATED_BASE;
    return *va2;
}

void write_vaddr(volatile void *va, word data) {
    volatile addr va2 = va + TRANSLATED_BASE;
    *va2 = data;
}
void print_test(volatile void *va, volatile void *pa) {
    MSG("Testing translation. pa: 0x%p, va: 0x%p\n", pa, va);
    MSG("[TEST] val: 0x%lx (pa) ?= 0x%lx (va)\n", read_paddr(pa), read_vaddr(va));
}

int vrs_test() {
    /* volatile uint64_t *a1 = 0xC0000000; */
    /* *a1 = 0xaaaa; */
    /* volatile uint64_t *a2 = 0x100000000; */
    /* MSG("%lx\n", *a1); */
    /* MSG("%lx\n", *a2); */

    addr ****pml4_table = (addr ****)0x0000UL;
    addr ***pdpt_table = (addr ***)0x1000UL;
    addr **pdir_table = (addr **)0x2000UL;
    addr *page_table = (addr *)0x3000UL;

    addr va = (addr)0x34567890;
    addr pa = (addr)0x4000;

    word pml4_i = ((word)va >> 39) & 0x1ff;
    word pdpt_i = ((word)va >> 30) & 0x1ff;
    word pdir_i = ((word)va >> 21) & 0x1ff;
    word page_i = ((word)va >> 12) & 0x1ff;
    /* MSG("pml4_i: %p\n", pml4_i); */
    /* MSG("pdpt_i: %p\n", pdpt_i); */
    /* MSG("pdir_i: %p\n", pdir_i); */
    /* MSG("page_i: %p\n", page_i); */

    // selectively filling entries to point va to an example pa
    write_paddr(pml4_table + pml4_i, (word)pdpt_table);
    write_paddr(pdpt_table + pdpt_i, (word)pdir_table);
    write_paddr(pdir_table + pdir_i, (word)page_table);
    write_paddr(page_table + page_i, (word)pa);

    write_paddr(pa, 0xda7a);
    print_test(va, pa);
    write_vaddr(va, 0xdeadbeefdeadbeef);
    print_test(va, pa);
    return 0;
}
