# Lexer

The lexer converts the input character stream of the specification file into a token stream.
This section explains and provides examples of the various tokens recognized and produced
by the lexer.



## Digits and Characters

The following rules recognize a single digit or character.


**Digit**
Recognizes a single digit from a base-ten number (e.g, 5)
```
DIGIT    := 0-9
```

**Binary Digit**
Recognizes a digit from a binary number (e.g., 0)
```
BINDIGIT := 01
```

**Octal Digit**
Recognizes a digit from an octal number (e.g., 7)
```
OCTDIGIT := 0-7
```

**Hex Digit**
Recognizes a digit from a hexadecimal number (e.g., a) in either uppercase or lowercase form.
```
HEXDIGIT := 0-9a-fA-F
```

**Alpha Character**
Recognizes a character from the ASCII alphabet in either lowercase or uppercase form.

```
ALPHA    := A-Za-z
```

**Alphanumeric Character**
Recognizes either a character from the ASCII alphabet in lowercase or uppercase form, or a digit.

```
ALPHANUM := ALPHA | DIGIT
```


## Numbers

Numbers represent a numeric literal. The lexer supports recognition of binary, octal,
hexadecimal and decimal numbers. The following describes the lexer rules.

The lexer will check for overflows when parsing the number.

**Decimal Numbers**


A base-ten number is at least one digit followed by zero or more
digits that may be separated by underscores (`"_"`)

```
NUM10 := DIGIT+ [ "_" | DIGIT ]*
```

Examples: `1000`, `2_300_500`, `999_99_9`


**Binary Number**

A binary number is then the string `"0b"` followed by one or more binary digits,
and zero or more binary digit groups separated by an underscore (`"_"`).
```
NUM2 := "0b" BINDIGIT+ [ "_" | BINDIGIT ]*
```

Examples: `0b0`, `0b1000_1000`

**Octal Number**

An octal number is then the string `"0o"` followed by one or more octal digits,
and zero or more octal digit groups separated by an underscore (`"_"`).

```
NUM8 := "0o" OCTDIGIT+ [ "_" | OCTDIGIT ]*
```

Examples: `0o755`, `0o7000_1234`

**Hexadecimal Number**

A hexadecimal number is the string `"0x"` followed by one or more hex digits,
and zero or more hex digit groups separated by an underscore (`"_"`). Both,
uppercase and lowercase numbers are supported.

```
NUM16 := "0x" HEXDIGIT+ [ "_" | HEXDIGIT+ ]*
```

Examples: `0x1000`, `0x4000_0000`

**Number**

A number is then either one of the four base numbers:

```
NUMBER := NUM10 | NUM16 | NUM8 | NUM2
```
Examples: `0o7000_1234`, `0x4000_0000`, `10`, `0b01001`