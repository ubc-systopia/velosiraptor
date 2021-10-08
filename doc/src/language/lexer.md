# Velosiraptor Language Grammer

## LEXEMES

```
    DIGIT := 0-9
    BINDIGIT := 01
    OCTDIGIT := 0-7
    HEXDIGIT := 0-9a-fA-F
    ALPHA := A-Za-z
    ALPHANUM := ALPHA | DIGIT
```

**Comments**
```
    blockcomment := /* ANY */
    linecomment  := // any EOL
```
**Keywords**
```
    KEYWORD := true | false | unit | import | const | let | if |
               else | assert | state | interface | Memory | Register |
               None | addr | size | int | bool
```

**Identifiers**
```
    IDENT := [ ALPHA | "_" ] [ALPHANUM | "_"]*
```

**Numbers**
```
    NUMBER := DIGIT+ ["_" | DIGIT ]*
            | "0x" HEXDIGIT+ ["_" | HEXDIGIT]+
            | "0o" OCTDIGIT+ ["_" | OCTDIGIT]+
            | "0b" BINDIGIT+ ["_" | BINDIGIT]+
```

**TOKENS**
```
    TOKEN =
    Dot,       // .
    Comma,     // ,
    Colon,     // :
    SemiColon, // ;

    // delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]

    // operators
    Plus,    // +
    Minus,   // -
    Star,    // *
    Slash,   // /
    Percent, // %  (remainder)
    LShift,  // <<
    RShift,  // >>

    // bitwise operators
    Xor, // ^  (xor)
    Not, // ~
    And, // &
    Or,  // |

    // logical operators
    LNot, // ! logical not
    LAnd, // &&
    LOr,  // ||

    // assignments
    Assign, // =

    // arrows
    RArrow,   // ->
    FatArrow, // =>

    // comparisons
    Eq, // ==
    Ne, // !=
    Lt, // <
    Gt, // >
    Le, // <=
    Ge, // >=

    // others, maybe not used
    At,         // @
    Underscore, // _
    DotDot,     // ..  for slices
    PathSep,    // ::
    Wildcard,   // ?
```