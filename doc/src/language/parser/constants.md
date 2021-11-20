# Constants

Specifications of translation hardware may include specific, constant values such as the
number of segment registers, the size of a page table, or the width of the addressing mode.
These values may be used at multiple locations. To avoid in-coherency, constants provide a
mechanism to give a constant value a name and re us that within the unit definitions.


## Grammer

```
CONST := KW_CONST IDENT COLON TYPEDEF EQ EXPR SEMICOLON
```

## Examples

```vrs
const PAGESIZE : int = 4096;
const ADDRESSWIDTH : int = 64;
const PAGE_TABLE_SIZE : int = PAGE_TABLE_ENTRIES * PAGE_TABLE_ENTRY_SIZE;
```

## Description

A constant definition assigns an identifier to an expression that must evaluate to a constant
value at compile time.

Each constant definition has a given [type](../lexer/types.md), and the expression must
produce a value of that type.

Constants can be defined on a global level, or within the scope of a unit.

Constants shall have a `SCREAMING_SNAKE_CASE` format.