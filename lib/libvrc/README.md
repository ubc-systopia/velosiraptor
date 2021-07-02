# Velosiraptor Compiler Support Library

This is the support library for the Velosiraptor compiler. It contains modules for
lexing and parsing the Velosiraptor specification files. (`*.vrs`).

## License

see the LICENSE file.

## Authors

Reto Achermann
Ilias Karimalis


## Components

The project consists of the following tools:

**lexer**
Lexes an input string or file and produces vector of tokens.

**parser**
Constructs an AST from the vector of tokens produced by the lexer.


## Dependencies

Install Rust for this project. See [RustUp](https://rustup.rs/).

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

```

## Contributing

Please follow the [naming and formatting conventions](https://doc.rust-lang.org/1.0.0/style/style/naming/README.html)
of Rust.

Run `cargo fmt` before committing.

## Building

To build the library

```
$ cargo build
```

## Documentation

```
$ cargo doc --no-deps
```


## Testing

```
$ cargo test
```

## TODO
- Add progress bar using the [inidicatif crate](https://docs.rs/indicatif/0.16.2/indicatif/)
