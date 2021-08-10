# Velosiraptor Compiler

This project contains a framework and tools to write specifications of
memory address translation hardware such as MMU, SMMUs and others.

## License

see the LICENSE file.

## Components

The project consists of the following tools:

**compiler**
The compiler turns VelosiRaptorSpecifications into operating systems code and
hardware platform modules.
The Velosiraptor Compiler parses specifications in the `*.vrs` (Velosiraptor Specification File)
format.


## Dependencies

Install Rust for this project. See [RustUp](https://rustup.rs/).

```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

```

Make sure the submodules are initialized properly
```
git submodule init
git submodule update
```

## Contributing

Please follow the [naming and formatting conventions](https://doc.rust-lang.org/1.0.0/style/style/naming/README.html)
of Rust.

Run `cargo fmt` before committing.

## Building

To build the compiler

```
$ cargo build
```

## Running

The compiler expects a `*.vrs` file. See `cargo run -h` for more options.

```
cargo run <*.vrs>
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
