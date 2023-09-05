// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! # VelosiParser Tests: Example Specs

// std includes

use std::path::{Path, PathBuf};
use std::rc::Rc;

use std::process::Command;

// use strip_ansi_escapes;

// our library
use velosiast::{AstResult, VelosiAst, VelosiAstUnit};
use velosihwgen::VelosiHwGen;
use velosiparser::{VelosiParser, VelosiParserError};
use velosisynth::create_models;
use velosisynth::Z3SynthFactory;

fn get_ast(vrs: &str) -> VelosiAst {
    match VelosiAst::from_file(vrs) {
        AstResult::Ok(ast) => {
            println!(" ok. Successfully created Ast.");
            ast
        }
        AstResult::Issues(ast, e) => {
            println!(" ok  (with warningsk)");
            println!(">>>>>>\n{}\n<<<<<<", e);
            ast
        }
        AstResult::Err(e) => {
            println!(" fail  (expected ok)");
            println!(">>>>>>\n{e}\n<<<<<<");
            panic!("Failed to construct AST.");
        }
    }
}

/// Tests the basic import functionality
#[test]
fn examples_parse() {
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        print!("  - Parsing {path_str} ...");

        match VelosiParser::parse_file(path_str, false) {
            Ok(_pt) => {
                println!(" ok. Successfully parsed.");
            }
            Err(VelosiParserError::LexingFailure { e }) => {
                println!(" fail  (lexer failure)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                panic!("Could not parse file");
            }
            Err(VelosiParserError::ParsingFailure { e }) => {
                println!(" fail  (parser failure)");
                println!(">>>>>>\n{}\n<<<<<<", e);
            }
            Err(e) => {
                println!(" fail  (unknown error)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                panic!("Could not parse file");
            }
        }
    }
}

/// Tests the basic import functionality
#[test]
fn examples_ast() {
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        print!("  - Parsing {path_str} ...");

        match VelosiAst::from_file(path_str) {
            AstResult::Ok(_ast) => {
                println!(" ok. Successfully created Ast.");
            }
            AstResult::Issues(_ast, e) => {
                println!(" ok  (with warningsk)");
                println!(">>>>>>\n{}\n<<<<<<", e);
                // panic!("Could not parse file");
            }
            AstResult::Err(e) => {
                println!(" fail  (expected ok)");
                println!(">>>>>>\n{e}\n<<<<<<");
                panic!("Failed to construct AST.");
            }
        }
    }
}

#[test]
fn examples_sanitycheck() {
    let mut ast = get_ast("examples/x86_64_pagetable.vrs");

    let mut synthfactory = Z3SynthFactory::new();
    synthfactory.num_workers(2).default_log_dir();

    let models = create_models(&ast);

    let mut had_errors = false;
    for unit in ast.units_mut() {
        match unit {
            VelosiAstUnit::Segment(u) => {
                if u.is_abstract {
                    continue;
                }

                print!(" - running sanity check for unit {}  ... ", u.ident());

                let seg = Rc::get_mut(u).expect("could not get mut ref!");

                let mut synth = synthfactory.create_segment(seg, models[seg.ident()].clone());

                let sanity_check = synth.sanity_check();
                if let Err(e) = sanity_check {
                    println!(" failed.  Sanity check failed.");
                    println!(">>>>>>\n{e}\n<<<<<<");

                    had_errors = true;
                } else {
                    println!(" ok.  Sanity check passed.");
                }
            }
            VelosiAstUnit::StaticMap(_) => {
                // no-op
            }
            VelosiAstUnit::Enum(_) => {
                // no-op
            }
        }
    }

    if had_errors {
        panic!("Sanity check failed.");
    }
}

#[test]
fn examples_distinguish() {
    let mut ast = get_ast("examples/x86_64_pagetable.vrs");

    let mut synthfactory = Z3SynthFactory::new();
    synthfactory.num_workers(2).default_log_dir();

    let models = create_models(&ast);

    let mut had_errors = false;
    for unit in ast.units_mut() {
        match unit {
            VelosiAstUnit::Segment(_) => {
                // no-op
            }
            VelosiAstUnit::StaticMap(_) => {
                // no-op
            }
            VelosiAstUnit::Enum(e) => {
                print!(" - running distinguish check for unit {}  ... ", e.ident());

                let e = Rc::get_mut(e).expect("could not get mut ref!");

                let mut synth = synthfactory.create_enum(e);

                if let Err(e) = synth.distinguish(&models) {
                    println!(" failed. Unable to distinguish variants");
                    println!(">>>>>>\n{e}\n<<<<<<");
                    had_errors = true;
                } else {
                    println!(" ok.  Units are distinguishable.");
                }
            }
        }
    }

    if had_errors {
        panic!("Sanity check failed.");
    }
}

/// Tests the basic import functionality
#[test]
fn examples_hwgen_fastmodels() {
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let name = vrs.file_stem().unwrap().to_string_lossy();

        println!("\nFile: {name}.vrs");

        let path_str = vrs.to_str().expect("could not create string from path");

        print!("  - Parsing {:40} ...", path_str);

        let ast = match VelosiAst::from_file(path_str) {
            AstResult::Ok(ast) => {
                println!(" ok");
                ast
            }
            AstResult::Issues(ast, e) => {
                println!(" ok  (with issues)");
                // println!(">>>>>>\n{e}\n<<<<<<");
                ast
            }
            AstResult::Err(e) => {
                println!(" fail  (expected ok)");
                println!(">>>>>>\n{e}\n<<<<<<");
                panic!("Failed to construct AST.");
            }
        };

        print!("  - generate hardware module ... ");

        let hwgen = VelosiHwGen::new_fastmodels(Path::new("./out"), name.clone().into());
        hwgen
            .prepare()
            .expect("could not prepare the hwgen backend");

        if let Err(e) = hwgen.generate(&ast) {
            println!(" failed!");
            println!(">>>>>>\n{e:?}\n<<<<<<");
        } else {
            println!(" ok");
        }

        hwgen.finalize(&ast).expect("could not finalize");

        print!("  - Compiling hardware module ... ");

        let outpath = Path::new("./out")
            .join(name.to_string())
            .join("hw/fastmodels");

        // run make
        let make = Command::new("make")
            .arg("unitlib")
            .env("TEST_MOCK_FAST_MODELS", "1")
            .current_dir(outpath)
            .output()
            .expect("Failed to execute command");

        if make.status.success() {
            let errs = String::from_utf8(make.stderr).unwrap();

            if errs.is_empty() {
                println!(" ok");
            } else {
                println!(" ok  (with issues)");
                println!(">>>>>>\n{errs}\n<<<<<<");
                panic!("Compilation resulted in warnings");
            }
        } else {
            println!(" failed. (errors during compilation");
            let errs = String::from_utf8(make.stdout).unwrap();
            println!(">>>>>>\n{errs}\n<<<<<<");

            let errs = String::from_utf8(make.stderr).unwrap();
            println!(">>>>>>\n{errs}\n<<<<<<");

            panic!("Compilation resulted in errors");
        }
    }
}
