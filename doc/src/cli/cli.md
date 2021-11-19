# Command Line Interface

This section explains the CLI interface of the VelosiRaptor compiler (`vrc`)

```
VelosiRaptor Compiler

USAGE:
    vrc [FLAGS] [OPTIONS] <input>

FLAGS:
    -h, --help       Prints help information
    -v               Sets the level of verbosity
    -V, --version    Prints version information

OPTIONS:
    -b, --backend <backend>    the code backend to use [rust, c]
    -e, --Werror <error>       Treat warnings to errors.
    -o, --output <output>      the output file
    -p, --pkg <pkg>            the package name to produce

ARGS:
    <input>    Sets the input file to use
```