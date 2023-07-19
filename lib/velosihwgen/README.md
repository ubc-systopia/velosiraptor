# Velosihwgen library

This library implements hardware generation from a [velosiast](../velosiast/).

Supported targets:

- ARM FastModels
- more to come...

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

To run an example

```
$ cargo ../../examples/x86_64_pagetable.vrs
```


## ARM FastModels

The first backend for hardware generation. WIP; folder structure of output is in
    (mod.rs)[./src/fastmodels/mod.rs].

### Usage

1. First, generate the units from the .vrs specification.

2. ARM FastModels is required to make and run the simulated hardware. (Here is a Dockerfile for a suitable environment)[https://gist.github.com/mlechu/9d238ae63a5fa3d6d66673f535996c85].

3. Run `make`.

4. ... more instructions to come

### Todo

- The C++ framework from which the generated code inherits should probably be part of this repo.
  For now it is cloned into the output directory during the `make` stage.
- Move away from a series of "push" operations to a C++ file. The generated files are not large.
- It might not be worth separating the hpp and cpp files. Alternatively, make the header simple and
  readable and quarantine the disaster code in the cpp