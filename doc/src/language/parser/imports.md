# Imports

Often, specifications may become large: for example, current page-table-based translation
schemes may result in multiple unit specifications (e.g., one for each level), and one
would like to separate different units into different files. Moreover, modularization
allows specifications to be reusable and to define constants in a single location.

## Grammar

```
IMPORT := KW_IMPORT IDENT SEMICOLON
```

## Example

```vrs
import x86_page_table_entry;
import x86_constants;
```

## Description

The evaluation of import directives is recursive: starting at the supplied root file name,
the compiler will resolve all imports recursively, while skipping already imported files.

Circular imports (e.g., `A` imports `B` and `B` imports `A`) will trigger an error.

Each specification file on its own must have all imports.