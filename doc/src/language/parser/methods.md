# Methods

Methods are mathematical functions: they perform a computation using the supplied
parameters and the current state of the translation unit. Generally, they are
*internal* to the translation hardware and cannot be invoked by system software.
Methods define certain procedures such as extracting the base address from the state,
or match supplied flags.

Methods contain statements and/or pre- and post-conditions that contain
[expressions](expressions.md).

## Grammar

```
METHOD       := KW_FN IDENT LPAREN ARGLIST RPAREN RARROW TYPE
                  REQUIRES* ENSURES* METHOD_BODY

REQUIRES     := KW_REQUIRES BOOL_EXPR SEMICOLON

ENSURES      := KW_ENSURES BOOL_EXPR SEMICOLON

ARGLIST      := [ ARG [COMMA ARG]* ]?

ARG          := IDENT COLON TYPE

METHOD_BODY  := RBRACE [ STMT ]* LBRACE

STMT := STMT_RETURN | STMT_LET | STMT_ASSERT | STMT_COND
STMT_RETURN  := KW_RETURN EXPR SEMICOLON
STMT_LET     := KW_LE IDENT COLON TYPE EQ EXPR SEMICOLON
STMT_ASSERT  := KW_ASSERT LPAREN BOOL_EXPR RPAREN SEMICOLON
STMT_COND    := KW_IF BOOL_EXPR LBRACE STMT+ RBRACE [KW_ELSE LBRACE STMT+ RBRACE]?
```

## Example

```vrs
fn get_base() -> addr {
    return state.entry.base << 12;
}

fn calc_size(val : int) -> int
  requires val < 1024;
  ensures calc_size(val) < 4096;
{
    return val * 4;
}
```


## Method Types

There are two distinct method types:

 1. External methods that are abstract and provide constraints to the code generation system.
 2. Internal methods with an implementation used by the translation hardware


## External Methods

External methods are generally abstract and correspond to operations that are executed by
system software. They are abstract because their implementation will be provided by the
code generation framework through the synthesis process.

These methods are useful to provide additional *constraints* to the code generation module. For more information see [Map/Unmap/Protect](mapunmapprotect.md)


**Map (required)**

This method ensures that the translation of a certain range (addr-size-tuple) produces
an address within the destination range. This is a state modifying operation.


**Unmap (optional)**

This method ensures that the range of addresses won't be mapped anymore.
This is a state modifying operation.

**Protect (optional)**

This method changes the protection of an already mapped region.
This is a state modifying operation.


## Internal methods

As mentioned above, internal methods provide a way to structure the implementation of the
translation hardware itself. This would correspond to procedures and functions that are
implemented by the simulator or the corresponding hardware description language.

**Translate (required)**

The [translate](translate.md) method must be defined for each unit. It defines the translation
semantics. This is a function state, address and flags, to a new address
(technically a *partial function*).

The translation function may make use of any other defined methods of the unit.

**Other Methods**

Additional methods can be declared in a unit context. All of them are
internal methods and are available as predicates and/or within the translation
method.

## Pre- and Post-Conditions

Methods can be augmented with pre- and post-conditions using the
`requires` and `ensures` clauses. This provides additional constraints
to the synthesizing step. The following example indicates the use
of pre- and post-conditions for the map function:
it requires that the range must be within some limit, the addresses
aligned to some page. Moreover, the function ensures that all addresses
within the range are translated properly.

```vrs
fn map(va: addr, sz: size, flags: int, pa: addr)
    requires va + sz < LIMIT;
    requires va % 4096 == 0;
    requires size == 4096;
    requires pa % 4096;
    ensures forall i : int :: 0 <= i && i < sz
                ==> translate(va + i, flags) == pa + i
{} // empty
```

## Statements

The body of the units are restricted to four statement kinds each of which
evaluate [expressions](expressions.md).

**Return**
Returns the value produced by the expression. Each branch must have a return statement.

**Let**
Defines a local variable.

**Assert**
Provides some additional constraint to the synthesizer

**Conditional**
Provides an if-then-else statement. Both branches must have a return statement.