# Expressions

Expressions produce either an integer or boolean value, and can be used as
part of the [statement](methods.md#statements) or [method pre- and post-conditions](methods.md#pre--and-post-conditions).

Expressions are heavily influenced by how rust handles expressions, albeit a bit
simiplified.


## Grammar

```
// currently no distinction in the grammar
BOOL_EXPR           :=  EXPR
ARITH_EXPR          :=  EXPR

EXPR                :=  TERM_EXPR [OP EXPR]?

TERM_EXPR           := NUM_LITERAL_EXPR
                     | BOOL_LITERAL_EXPR
                     | FN_CALL_EXPR
                     | SLICE_EXPR
                     | ELEMENT_EXPR
                     | IDENT_EXPR

NUM_LITERAL_EXPR    := NUMBER
BOOL_LITERAL_EXPR   := BOOLEAN
FN_CALL_EXPR        := IDENT LPAREN [EXPR [COMMA EXPR]* ]? RPAREN
SLICE_EXPR          := IDENT RBRAK RANGE_EXPR LBRAK
RANGE_EXPR          := ARITH_EXPR DOTDOT ARITH_EXPR
ELEMENT_EXPR        := IDENT RBRAK ARITH_EXPR LBRAK
IDENT_EXPR          := IDENT
```




## Operator Precedence

The operator precedence roughly follows the [Rust model](https://doc.rust-lang.org/reference/expressions.html#expression-precedence).



|Precedence | Operators         | Associativity               |  Example                                             |
|-----------|-------------------|-----------------------------|------------------------------------------------------|
| Strong    | Field expression  | left to right               | `a.b.c`                                              |
|           | Fn Calls / Array  |                             | `a()` `a[]`                                          |
|           | Unary ! & ~       |                             | `!a` `~a` `&a`                                       |
|           | Multiply / Div    | left to right               | `a * b` `a / b` `a % b`                              |
|           | Plus Minus        | left to right               | `a + b` `a - b`                                      |
|           | Shifts            | left to right               | `a << b` `a >> b`                                    |
|           | Bitwise And       | left to right               | `a & b`                                              |
|           | Bitwise Xor       | left to right               | `a ^ b`                                              |
|           | Bitwise Or        | left to right               | `a \| b`                                             |
|           | Comparisons       | Require parenthesis         | `a == b` `a != b` `a < b` `a > b` `a <= b` `a >= b`  |
|           | Logical And       | left to right               | `a && b`                                             |
|           | Logical Or        | left to right               | `a || b`                                             |
|           | Implies           | left to right               | `a ==> b`                                            |
| Weak      | Range Expression  | Require parenthesis         | `a..b`                                                |




## Quantifier Expressions

A quantifier expression produces a boolean value based on whether the mathematical
quantifier expression (`forall` or `exists`) holds.

**Grammar**
```
QUANTIFIER_EXPR := FORALL_EXPR | EXISTS_EXPR

FORALL_EXPR := KW_FORALL ARGLIST PATHSEP BOOL_EXPR
EXISTS_EXPR := KW_EXISTS ARGLIST PATHSEP BOOL_EXPR
```

**Example**
```vrs
forall x : int :: a + x > 0
```

