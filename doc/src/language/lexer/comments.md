# Comments

The VeloSiraptor language uses similar comment style like C / Rust / Java.

## Line Comments

Line comments mark everything from the start of comment marker `//` up to and including
the end of line marker as a comment.

```
LINECOMMENT := "//" ABY EOL
```

Example

```
// this is a comment
```

## Block Comments

A block comment takes everything from the start of comment marker `/*` up to and including
to the end of comment marker `*/` as a comment.

```
BLOCKCOMMENT := /* ANY */
```

Example
```
/* this is a
multiline comment */

/* this is a comment */ 1234
```

**Nesting** Block comments may contain line comments, but block comments must not be nested.