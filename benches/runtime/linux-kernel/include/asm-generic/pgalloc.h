/* SPDX-License-Identifier: GPL-2.0 */
#ifndef __ASM_GENERIC_PGALLOC_H
#define __ASM_GENERIC_PGALLOC_H

#include <stdlib.h>
#include <asm-generic/bug.h>

#ifdef CONFIG_MMU

#define GFP_PGTABLE_KERNEL	(GFP_KERNEL | __GFP_ZERO)
#define GFP_PGTABLE_USER	(GFP_PGTABLE_KERNEL | __GFP_ACCOUNT)

/**
 * __pte_alloc_one - allocate memory for a PTE-level user page table
 * @mm: the mm_struct of the current context
 * @gfp: GFP flags to use for the allocation
 *
 * Allocate memory for a page table and ptdesc and runs pagetable_pte_ctor().
 *
 * This function is intended for architectures that need
 * anything beyond simple page allocation or must have custom GFP flags.
 *
 * Return: `struct page` referencing the ptdesc or %NULL on error
 */
static inline pgtable_t __pte_alloc_one_noprof(struct mm_struct *mm, gfp_t gfp)
{
	void *mem=aligned_alloc(PAGE_SIZE, PAGE_SIZE);
	memset(mem, 0, PAGE_SIZE);
	return mem;
}
#define __pte_alloc_one(...)	__pte_alloc_one_noprof(__VA_ARGS__)

#ifndef __HAVE_ARCH_PTE_ALLOC_ONE
/**
 * pte_alloc_one - allocate a page for PTE-level user page table
 * @mm: the mm_struct of the current context
 *
 * Allocate memory for a page table and ptdesc and runs pagetable_pte_ctor().
 *
 * Return: `struct page` referencing the ptdesc or %NULL on error
 */
static inline pgtable_t pte_alloc_one_noprof(struct mm_struct *mm)
{
	return __pte_alloc_one_noprof(mm, GFP_PGTABLE_USER);
}
#define pte_alloc_one(...)	pte_alloc_one_noprof(__VA_ARGS__)
#endif

/*
 * Should really implement gc for free page table pages. This could be
 * done with a reference count in struct page.
 */

/**
 * pte_free - free PTE-level user page table memory
 * @mm: the mm_struct of the current context
 * @pte_page: the `struct page` referencing the ptdesc
 */
static inline void pte_free(struct mm_struct *mm, struct page *pte_page)
{
	assert(!"NYI");
}


#if CONFIG_PGTABLE_LEVELS > 2

#ifndef __HAVE_ARCH_PMD_ALLOC_ONE
/**
 * pmd_alloc_one - allocate memory for a PMD-level page table
 * @mm: the mm_struct of the current context
 *
 * Allocate memory for a page table and ptdesc and runs pagetable_pmd_ctor().
 *
 * Allocations use %GFP_PGTABLE_USER in user context and
 * %GFP_PGTABLE_KERNEL in kernel context.
 *
 * Return: pointer to the allocated memory or %NULL on error
 */
static inline pmd_t *pmd_alloc_one_noprof(struct mm_struct *mm, unsigned long addr)
{
	void *mem=aligned_alloc(PAGE_SIZE, PAGE_SIZE);
	memset(mem, 0, PAGE_SIZE);
	return mem;
}
#define pmd_alloc_one(...)	pmd_alloc_one_noprof(__VA_ARGS__)
#endif

#ifndef __HAVE_ARCH_PMD_FREE
static inline void pmd_free(struct mm_struct *mm, pmd_t *pmd)
{
	BUG_ON((unsigned long)pmd & (PAGE_SIZE-1));
	free(pmd);
}
#endif

#endif /* CONFIG_PGTABLE_LEVELS > 2 */

#if CONFIG_PGTABLE_LEVELS > 3

static inline pud_t *__pud_alloc_one_noprof(struct mm_struct *mm, unsigned long addr)
{
	void *mem=aligned_alloc(PAGE_SIZE, PAGE_SIZE);
	memset(mem, 0, PAGE_SIZE);
	return mem;
}
#define __pud_alloc_one(...)	__pud_alloc_one_noprof(__VA_ARGS__)

#ifndef __HAVE_ARCH_PUD_ALLOC_ONE
/**
 * pud_alloc_one - allocate memory for a PUD-level page table
 * @mm: the mm_struct of the current context
 *
 * Allocate memory for a page table using %GFP_PGTABLE_USER for user context
 * and %GFP_PGTABLE_KERNEL for kernel context.
 *
 * Return: pointer to the allocated memory or %NULL on error
 */
static inline pud_t *pud_alloc_one_noprof(struct mm_struct *mm, unsigned long addr)
{
	return __pud_alloc_one_noprof(mm, addr);
}
#define pud_alloc_one(...)	pud_alloc_one_noprof(__VA_ARGS__)
#endif

static inline void __pud_free(struct mm_struct *mm, pud_t *pud)
{
	BUG_ON((unsigned long)pud & (PAGE_SIZE-1));
	free(pud);
}

#ifndef __HAVE_ARCH_PUD_FREE
static inline void pud_free(struct mm_struct *mm, pud_t *pud)
{
	__pud_free(mm, pud);
}
#endif

#endif /* CONFIG_PGTABLE_LEVELS > 3 */

#ifndef __HAVE_ARCH_PGD_FREE
static inline void pgd_free(struct mm_struct *mm, pgd_t *pgd)
{
	pagetable_free(virt_to_ptdesc(pgd));
}
#endif

#endif /* CONFIG_MMU */

#endif /* __ASM_GENERIC_PGALLOC_H */