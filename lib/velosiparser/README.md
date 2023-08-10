# Velosiparser Library

This library implements the Velosiparser, the parser for the Velosiraptor Specification Language
source files (*.vrs). The parser consumes a sequence of lexemes produced by the Velosilexer and
produces a parse tree.


## License

see the LICENSE file.


## Authors

Reto Achermann


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

To build the source code documentation, simply run the cargo doc command.

```
$ cargo doc --no-deps
```


## Testing

To run tests for the parser, use the cargo test command.

```
$ cargo test
```
