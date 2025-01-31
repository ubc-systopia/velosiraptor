#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <stdbool.h>

#include "velosiraptor/x8664pml4_unit.h"

extern void *linux_bench_init();
extern int linux_bench_map_one(void *st, unsigned long addr, unsigned long paddr);
extern int linux_bench_unmap_one(void *st, unsigned long addr, unsigned long _paddr);
extern int linux_bench_protect_one(void *st, unsigned long addr, unsigned long _paddr);

extern void *barrelfish_init();
extern int barrelfish_kernel_map_one(void *st, unsigned long addr, unsigned long paddr);
extern int barrelfish_kernel_protect_one(void *st, unsigned long addr, unsigned long paddr);
extern int barrelfish_kernel_unmap_one(void *st, unsigned long addr, unsigned long paddr);

#define PAGE_SIZE 4096
#define BENCHMARK_RUNS 200
#define BENCHMARK_DRYRUNS 5

static unsigned long measurements[BENCHMARK_RUNS+BENCHMARK_DRYRUNS+1];

#define timpespec_diff(t1, t2) ((t2.tv_sec - t1.tv_sec) * 1000000000 + (t2.tv_nsec - t1.tv_nsec))

paddr_t memory_alloc(size_t sz, paddr_t align) {
    return (paddr_t)aligned_alloc(PAGE_SIZE, PAGE_SIZE);
}

void memory_free(paddr_t pa, size_t sz) {
    free((void *)pa);
}

vaddr_t local_phys_to_mem(paddr_t pa) {
    return pa;
}

paddr_t mem_to_local_phys(vaddr_t va) {
    return va;
}

static int velosiraptor_map_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pml4__t *vroot = st;
    flags_t flags = { writable:1, readable: 1};
    size_t r = x8664pml4_map(vroot, vaddr, PAGE_SIZE, flags, paddr);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_protect_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pml4__t *vroot = st;
    flags_t flags = { writable:0, readable: 1};
    size_t r =  x8664pml4_protect(vroot, vaddr, PAGE_SIZE, flags);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_unmap_one(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pml4__t *vroot = st;
    size_t r = x8664pml4_unmap(vroot, vaddr, PAGE_SIZE);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_pte_map(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pagetable__t *vroot = st;
    flags_t flags = { writable:1, readable: 1};
    size_t r = x8664pagetable_map(vroot, vaddr, PAGE_SIZE, flags, paddr);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_pte_protect(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pagetable__t *vroot = st;
    flags_t flags = { writable:0, readable: 1};
    size_t r =  x8664pagetable_protect(vroot, vaddr, PAGE_SIZE, flags);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

static int velosiraptor_pte_unmap(void *st, vaddr_t vaddr, paddr_t paddr) {
    x8664pagetable__t *vroot = st;
    size_t r = x8664pagetable_unmap(vroot, vaddr, PAGE_SIZE);
    // printf("Result: %zu\n", r);
    return (r != PAGE_SIZE);
}

typedef int (*run_fn_t)(void *st, vaddr_t, paddr_t);

static void run_benchmark(const char *label, run_fn_t f, void *st, vaddr_t vaddr, paddr_t paddr) {
    int r;
    printf("%s: ", label);
    for (int i = 0; i <= BENCHMARK_RUNS + BENCHMARK_DRYRUNS; i++) {
        struct timespec t_start, t_end;
        clock_gettime(CLOCK_MONOTONIC, &t_start);
        r = f(st, vaddr, paddr);
        vaddr += PAGE_SIZE;
        assert(r ==0);
        r = f(st, vaddr, paddr);
        vaddr += PAGE_SIZE;
        assert(r ==0);
        clock_gettime(CLOCK_MONOTONIC, &t_end);

        measurements[i] = timpespec_diff(t_start, t_end) / 2;
        if (i >= BENCHMARK_DRYRUNS) {
            printf("%ld ", measurements[i]);
        }
    }
    printf("\n");
}



int main() {
    unsigned long vaddr = 0x0;
    unsigned long paddr = 0x1000;
    void *linux_st = linux_bench_init();
    run_benchmark("Linux-x86_64-Map", linux_bench_map_one, linux_st, vaddr, paddr);
    run_benchmark("Linux-x86_64-Protect", linux_bench_protect_one, linux_st, vaddr, paddr);
    run_benchmark("Linux-x86_64-Unmap", linux_bench_unmap_one, linux_st, vaddr, paddr);

    x8664pml4__t vroot;
    x8664pml4_alloc(&vroot);
    run_benchmark("Velosiraptor-x86_64-Map", velosiraptor_map_one, &vroot, vaddr, paddr);
    run_benchmark("Velosiraptor-x86_64-Protect", velosiraptor_protect_one,  &vroot, vaddr, paddr);
    run_benchmark("Velosiraptor-x86_64-Unmap", velosiraptor_unmap_one,  &vroot, vaddr, paddr);


    void *st = barrelfish_init();
    run_benchmark("Barrelfish-PTable-Map", barrelfish_kernel_map_one, st, vaddr, paddr);
    run_benchmark("Barrelfish-PTable-Protect", barrelfish_kernel_protect_one, st, vaddr, paddr);
    run_benchmark("Barrelfish-PTable-Unmap", barrelfish_kernel_unmap_one, st, vaddr, paddr);

    x8664pagetable__t pt;
    x8664pagetable_alloc(&pt);
    run_benchmark("Velosiraptor-PTable-Map", velosiraptor_pte_map, &pt, vaddr, paddr);
    run_benchmark("Velosiraptor-PTable-Protect", velosiraptor_pte_protect,  &pt, vaddr, paddr);
    run_benchmark("Velosiraptor-PTable-Unmap", velosiraptor_pte_unmap,  &pt, vaddr, paddr);

}