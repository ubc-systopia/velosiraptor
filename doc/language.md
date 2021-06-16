# The VelosiRaptor Specification Language

This document describes the VelosiRaptor Specification Language and its
elements. The language is designed to intuitively describe address translation
hardware, including its translation semantics, state and software visible
interface. The langauge serves as a basis for generating both, an OS driver
and a (simulated) hardware component implementing the translation hardware.


## Basic Constructs

We first define the basic building blocks of the keywords such as keywords,
identifiers and so on.

First, we define the following basic sets of characters for expressing the
language lexemes.

```
    NUMERIC      := [ 0-9 ]
    ALPHA        := [ a-zA-Z ]
    ALPHANUMERIC := [ :ALPHA: | :NUMERIC: ]
```

The identifier is then a letter, followed by zero or more alphanumeric
characters.

```
IDENTIFIER := [ :ALPHA: ]  [ :ALPHANUMERIC: ]*
```

## Keywords

The language has the following keywords

```
    unit
    import
    memory
    register
    map
```

## Specification Files

The VelosiRaptor Specification Language is stored in "VelosiRaptor Specification" files
with the extension `*.vrs`. The files should be standard ASCII and use UNIX-style new
lines (`\n`). The files contain two language constructs: `import` statements and `unit`
definitions.

Example:

```
    example.vrs
```

## Import Statements

The VelosiRaptor provides features to import definitions from other VelosiRaptor
Specification Files. This provides functionality for modular and reusable definitions.
The VelosiRaptor compiler will recursively parse the imported files and add the
defined types to the parse state. Currently, we use simple imports such as:

Example:
```
    import table;
```

In the future we may add functionality to do more selective imports such as listing
the types / definitions we are interested in.
```
    from table import L1;
    import table::L1;
```

## Unit Definitions

The unit specifies a translation. It composes previously defined units, or base types.

```
unit L1Table {
    ...
};
```

## Extending Types (Inheritance)

The VelosiRaptor specification language has two abstract, configurable base types:

 * `Segment`
 * `Assoc`


```
unit L1TableEntry : Segment {
    ...
};
```

```
unit BridgeWindow : Assoc {
    ...
};
```


Likewise, we can also extend previously defined types.

## Static Maps


## Expressing State


## Translation Semantics


## Adding Constraints
