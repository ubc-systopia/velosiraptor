# Static Maps

A static map defines a fixed translation function from input address ranges to output
address ranges (destination units). The map is fixed at compile time, and thus cannot
be configured at runtime.

Static maps are used to divide the input address range of a unit, and steer
translations to configurable units. A page table, for instance, is a static map that
selects the page table entry for the translation.

# Grammar

```
MAP := KW_STATICMAP ASSIGN LBRACK [ MAP_EXPLICIT_LIST | MAP_LIST_CMPR ]  RBRACK SEMICOLON

MAP_EXPLICIT_LIST := MAP_ELEMENT [ COMMA MAP_ELEMENT ]*
MAP_LIST_COMPR := MAP_ELEMENT KW_FOR IDENT KW_IN RANGE_EXPR

MAP_ELEMENT := MAP_SRC? MAP_DST

MAP_SRC  := RANGE_EXPR RARROW

MAP_DEST := IDENT LPAREN EXPR_LIST RPAREN AT EXPR

EXPR_LIST := [ EXPR [ COMMA EXPR ]* ]?

```

## Examples

```vrs

// simple, explicit list
staticmap = [
    PageTableEntry(base + 0),
    PageTableEntry(base + 1),
];

// comprehension
staticmap = [
    PageTableEntry(base + i) for i in 0..512
];

// with input and output ranges
staticmap = [
    0x0000..0x0fff => DestUnit(base) @ 0x1000
]

```

## Address Range Rules

An element of a static map has a well-defined input address range `[base..limit]`.

The input address ranges of any two entries must not overlap.

The input address range must not exceed the available addressing width of the
next unit.

## Output Address Calculation

The output address, i.e., the address that will become the input address of the
destination unit, is calculated as follows:

```
OUT_ADDR = IN_ADDR - ENTRY_BASE + OFFSET
```

Where, `ENTRY_BASE` is the base address of the matching entry of the map, and
`OFFSET` is the value of the `@` expression.


The output address range must not exceed the available addressing width of the
next unit.
