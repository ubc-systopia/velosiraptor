# Velosilexer Library

This library implements the Velosilexer, the lexer for the Velosiraptor Specification Language
source files (*.vrs). The lexer converts an input stream (file or string) into a sequence of
tokens that can the be consumed by a parser. It strips out white space and comments.


## License

see the LICENSE file.


## Authors

Reto Achermann


## Building

To build the lexer library and the example binrary simply run the following command

```
$ cargo build
```

## Running

To run the lexer on input from stdin use:

```
$ echo "foo" | cargo run
```

Or you can run the lexer on a file using

```
$ cargo run -- <file>
```


## Documentation

You can generate the documentation using cargo doc.

```
$ cargo doc --no-deps
```


## Contributing and Testing

Please follow the [naming and formatting conventions](https://doc.rust-lang.org/1.0.0/style/style/naming/README.html)
of Rust and run `cargo fmt` before committing.

To run the tests for the library simply run the following command

```
$ cargo test
```
