# Specification Language

This section describes the VelosiRaptor Specification Language (VSL) using the tokens outlined
in the [previous section](../lexer/lexer.md).

## Specification Files

A translation hardware component is specified in a VelosiRaptor Specification Language file
(`*.vrs`). At the top level, there are three possible constructs:

 1. [Imports](imports.md) to include other specification files.
 2. [Constants](constants.md) that defines globally visible constants.
 3. [Units](units.md) that specify translation hardware components.

The unit is the *core* element of the specification language.

**Encoding**
The encoding of the file should be plain ASCII, and process

**Naming**
Currently all specification files should be placed in the same directory, and must have
a filename in the form of an [identifier](../lexer/identifiers.md) followed by the `*.vrs` extension.

There is no restriction regarding the name of the unit specified in the file, and the filename
itself.


## Example

```vrs
// A sample specification file

// import of the global constants, defined in another file
import globals;

// define some constants used in the spec
const NUM_ENTRIES : int = 512;
const PAGE_TABLE_SIZE : int = NUM_ENTRIES * POINTER_SIZE;

// define the page table unit
unit PageTable(base : addr) {
    state = ...
    interface = ...

    fn translate(va: addr, flags: int) -> addr {
        ...
    }
}


```