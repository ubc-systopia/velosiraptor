#include <vrs_test.h>

typedef unsigned long addr;

#define SETUP_BASE        (void *)0x1C0000000
#define TRANSLATABLE_BASE (void *)0x0C0000000

int vrs_test() {
    // cr3 val = 0x0

    addr ****pml4_table = (addr ****)0x1C0000000;
    addr ***pdpt_table = (addr ***)0x1C0001000;
    addr **pdir_table = (addr **)0x1C0002000;
    addr *page_table = (addr *)0x1C0003000;

    addr va = 0x12345678abcd;
    int pml4_i = (va >> 39) & 0x1ff;
    int pdpt_i = (va >> 30) & 0x1ff;
    int pdir_i = (va >> 21) & 0x1ff;
    int page_i = (va >> 12) & 0x1ff;

    // selectively filling entries to point va to an example pa
    pml4_table[pml4_i] = pdpt_table;
    pdpt_table[pdpt_i] = pdir_table;
    pdir_table[pdir_i] = page_table;
    page_table[page_i] = 0x99999990;  // paddr

    // todo access

    return 0;
}
