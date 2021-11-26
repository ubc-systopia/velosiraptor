# Identifiers

Identifiers represent symbols and names in the VelosiRaptor language and thus play a central role
when specifying translation units.

## Identifier

An identifier begins with either an alpha character or an underscore, and may be followed by a
sequence of alphanumeric characters and underscores.

```
IDENT := [ ALPHA | "_" ] [ALPHANUM | "_" ]*
```

Example: `foo`, `foo_bar`, `foobar_1234`

## Naming Conventions

The VelosiRaptor language roughly follows the naming convention of [Rust](https://rust-lang.github.io/api-guidelines/naming.html)
The compiler will display a warning

| Item         | Price                  |
|--------------|------------------------|
| Unit Name    | `CamelCase`            |
| Method Name  | `snake_case`           |
| Constants    | `SCREAMING_SNAKE_CASE` |
| Parameters   | `snake_case`           |
| Variables    | `snake_case`           |


