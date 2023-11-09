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

use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

// use strip_ansi_escapes;

// our library
use velosiast::{AstResult, VelosiAst, VelosiAstUnit};
use velosicodegen::VelosiCodeGen;
use velosicomposition::Relations;
use velosiparser::{VelosiParser, VelosiParserError};
use velosisynth::create_models;
use velosisynth::Z3SynthFactory;

fn get_ast(vrs: &str) -> VelosiAst {
    match VelosiAst::from_file(vrs) {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, _e) => ast,
        AstResult::Err(e) => {
            println!("    =>  failed  (constructing AST failed");
            println!("     +-------------------------------------------------------------------");
            for l in e.to_string().lines() {
                println!("     | {}", l);
            }
            println!("     +-------------------------------------------------------------------");
            panic!("Failed to construct the AST");
        }
    }
}

fn get_osspec(vrs: &str) -> VelosiAst {
    match VelosiAst::osspec_from_file(vrs) {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, _e) => ast,
        AstResult::Err(e) => {
            println!("    =>  failed  (constructing AST failed for osspec)");
            println!("     +-------------------------------------------------------------------");
            for l in e.to_string().lines() {
                println!("     | {}", l);
            }
            println!("     +-------------------------------------------------------------------");
            panic!("Failed to construct the AST for osspec");
        }
    }
}

/// Tests the basic import functionality
#[test]
fn examples_parse() {
    println!("\n\nPARSING EXAMPLES");
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        println!("\n  @ Parsing {path_str} ...");

        let t_start = Instant::now();
        let pst = VelosiParser::parse_file(path_str, false);
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();

        match pst {
            Ok(_pt) => {
                println!("    => ok. Successfully parsed.    {t_elapsed_ms} ms");
            }
            Err(VelosiParserError::LexingFailure { e }) => {
                println!("    =>  failed  (lexer failure)    {t_elapsed_ms} ms");
                println!(
                    "     +-------------------------------------------------------------------"
                );
                for l in e.to_string().lines() {
                    println!("     | {}", l);
                }
                println!(
                    "     +-------------------------------------------------------------------"
                );
                panic!("Failed to parse.");
            }
            Err(VelosiParserError::ParsingFailure { e }) => {
                println!("    =>  failed  (parsing failure)    {t_elapsed_ms} ms");
                println!(
                    "     +-------------------------------------------------------------------"
                );
                for l in e.to_string().lines() {
                    println!("     | {}", l);
                }
                println!(
                    "     +-------------------------------------------------------------------"
                );
                panic!("Failed to parse.");
            }
            Err(e) => {
                println!("    =>  failed  (unknown error ok)    {t_elapsed_ms} ms");
                println!(
                    "     +-------------------------------------------------------------------"
                );
                for l in e.to_string().lines() {
                    println!("     | {}", l);
                }
                println!(
                    "     +-------------------------------------------------------------------"
                );
                panic!("Failed to parse.");
            }
        }
    }
}

/// Tests the basic import functionality
#[test]
fn examples_ast() {
    println!("\n\nCONSTRUCT AST EXAMPLES");
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        let path_str = vrs.to_str().expect("could not create string from path");

        println!("\n  @ Parsing {path_str} ...");

        let t_start = Instant::now();
        let ast = VelosiAst::from_file(path_str);
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();

        match ast {
            AstResult::Ok(_ast) => {
                println!("    => ok. Successfully created Ast.    {t_elapsed_ms} ms");
            }
            AstResult::Issues(_ast, e) => {
                println!("    => ok  (with warnings)    {t_elapsed_ms} ms");
                println!(
                    "     +-------------------------------------------------------------------"
                );
                for l in e.to_string().lines() {
                    println!("     | {}", l);
                }
                println!(
                    "     +-------------------------------------------------------------------"
                );
            }
            AstResult::Err(e) => {
                println!("    =>  failed  (expected ok)    {t_elapsed_ms} ms");
                println!(
                    "     +-------------------------------------------------------------------"
                );
                for l in e.to_string().lines() {
                    println!("     | {}", l);
                }
                println!(
                    "     +-------------------------------------------------------------------"
                );
                panic!("Failed to construct AST.");
            }
        }
    }
}

#[test]
fn examples_sanitycheck() {
    println!("\n\nSANITY CHECK EXAMPLES");
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        println!("  @ Sanity Check: {}", vrs.display());

        let t_start = Instant::now();
        let mut ast = get_ast(vrs.display().to_string().as_str());
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - AST creation: {t_elapsed_ms} ms");

        let mut synthfactory = Z3SynthFactory::new();
        synthfactory.num_workers(2).default_log_dir();

        let t_start = Instant::now();
        let models = create_models(&ast);
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - Model creation: {t_elapsed_ms} ms");

        let mut had_errors = false;
        for unit in ast.units_mut() {
            match unit {
                VelosiAstUnit::Segment(u) => {
                    if u.is_abstract {
                        continue;
                    }

                    println!("    - Unit: {}  ... ", u.ident());

                    let seg = Rc::get_mut(u).expect("could not get mut ref!");

                    let mut synth = synthfactory.create_segment(seg, models[seg.ident()].clone());

                    let t_start = Instant::now();
                    let sanity_check = synth.sanity_check();
                    let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();

                    if let Err(e) = sanity_check {
                        println!("      =>  failed  (sanity check failed    {t_elapsed_ms} ms");
                        println!("       +-------------------------------------------------------------------");
                        for l in e.to_string().lines() {
                            println!("       | {}", l);
                        }
                        println!("       +-------------------------------------------------------------------");
                        had_errors = true;
                    } else {
                        println!("      =>  OK (sanity check passed)    {t_elapsed_ms} ms");
                    }
                }
                VelosiAstUnit::StaticMap(_) => {
                    // no-op
                }
                VelosiAstUnit::Enum(_) => {
                    // no-op
                }
                VelosiAstUnit::OSSpec(_) => {
                    // no-op
                }
            }
        }

        if had_errors {
            panic!("    => Sanity check failed.");
        } else {
            println!("    => all units ok!");
        }
    }
}

#[test]
fn examples_distinguish() {
    println!("\nDISTINGUISHABILITLY EXAMPLES");
    let d = PathBuf::from("examples");
    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        println!("  @ Distinguishability Check {}", vrs.display());

        let t_start = Instant::now();
        let mut ast = get_ast(vrs.display().to_string().as_str());
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - AST creation: {t_elapsed_ms} ms");

        let mut synthfactory = Z3SynthFactory::new();
        synthfactory.num_workers(2).default_log_dir();

        let t_start = Instant::now();
        let models = create_models(&ast);
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - Model creation: {t_elapsed_ms} ms");

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
                    println!("    - Unit {}  ... ", e.ident());

                    let e = Rc::get_mut(e).expect("could not get mut ref!");

                    let mut synth = synthfactory.create_enum(e);

                    let t_start = Instant::now();
                    let dist = synth.distinguish(&models);
                    let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();

                    if let Err(e) = dist {
                        println!("      =>  failed  (distinguishability check failed    {t_elapsed_ms} ms");
                        println!("       +-------------------------------------------------------------------");
                        for l in e.to_string().lines() {
                            println!("       | {}", l);
                        }
                        println!("       +-------------------------------------------------------------------");
                        had_errors = true;
                    } else {
                        println!(
                            "      =>  OK (distinguishability check passed)    {t_elapsed_ms} ms"
                        );
                    }
                }
                VelosiAstUnit::OSSpec(_) => {
                    // no-op
                }
            }
        }

        if had_errors {
            panic!("Sanity check failed.");
        }
    }
}

#[test]
fn examples_synth() {
    println!("\nSYNTHESIS EXAMPLES");
    let d = PathBuf::from("examples");

    let ncores = std::cmp::max(
        std::thread::available_parallelism()
            .map(|i| i.into())
            .unwrap_or(1)
            / 2,
        1,
    );

    for f in d.read_dir().expect("could not read example directory") {
        let vrs = f.expect("could not read directory entry").path();

        if vrs.is_dir() {
            continue;
        }

        println!("  @ Synthesis Check {}", vrs.display());

        let t_start = Instant::now();
        let mut ast = get_ast(vrs.display().to_string().as_str());
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - AST creation: {t_elapsed_ms} ms");

        let mut synthfactory = Z3SynthFactory::new();
        synthfactory.num_workers(ncores).default_log_dir();

        let t_start = Instant::now();
        let models = create_models(&ast);
        let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
        println!("    - Model creation: {t_elapsed_ms} ms");

        let mut had_errors = false;
        for unit in ast.units_mut() {
            match unit {
                VelosiAstUnit::Segment(unit) => {
                    if unit.is_abstract {
                        // don't handle abstract units
                        continue;
                    }

                    println!("    - Unit {}", unit.ident());

                    let seg =
                        Rc::get_mut(unit).expect("Could not get mutable reference to segment!");

                    let t_0 = Instant::now();
                    let mut synth = synthfactory.create_segment(seg, models[seg.ident()].clone());
                    let t_init_ms = Instant::now().duration_since(t_0).as_millis();

                    let t_start = Instant::now();
                    synth.synthesize(false);
                    let t_synth = Instant::now().duration_since(t_start).as_millis();

                    let t_total = Instant::now().duration_since(t_0).as_millis();

                    let t_map = synth.t_map_synthesis.as_millis();
                    let t_protect = synth.t_protect_synthesis.as_millis();
                    let t_unmap = synth.t_unmap_synthesis.as_millis();

                    if synth.finalize().is_ok() {
                        println!("      => Ok  Synthesis completed    {t_total} ms = {t_init_ms} ms + {t_synth} ms ");
                        println!("            - map: {t_map} ms, unmap: {t_unmap} ms, protect: {t_protect} ms", );
                    } else {
                        println!("      => Failed");
                        had_errors = true;
                    }
                    // no-op
                }
                VelosiAstUnit::StaticMap(_) => {
                    // no-op
                }
                VelosiAstUnit::Enum(_) => {
                    // no-op
                }
                VelosiAstUnit::OSSpec(_) => {
                    // no-op
                }
            }
        }

        if had_errors {
            panic!("Sanity check failed.");
        }
    }
}

type CodeGenConstructor = fn(&Path, String) -> VelosiCodeGen;

#[cfg(test)]
fn examples_codegen(lang: &str, new_codegen_fn: CodeGenConstructor) {
    let mut outdir = PathBuf::from("out");

    println!("\n\nOS GEN EXAMPLES {lang}");
    let translationspecs = PathBuf::from("examples");
    let osspecs = PathBuf::from("examples/osspec");
    for f in translationspecs
        .read_dir()
        .expect("could not read example directory")
    {
        let vrs = f.expect("could not read directory entry").path();
        if vrs.is_dir() {
            continue;
        }

        if !matches!(
            vrs.display().to_string().as_str(),
            "examples/singlesegment.vrs" | "examples/multisegment.vrs"
        ) {
            continue;
        }

        for osspec in osspecs
            .read_dir()
            .expect("could not read the OS Spec directory")
        {
            let os = osspec.expect("could not read directory entry").path();

            outdir.push(os.file_stem().unwrap().to_str().unwrap());

            println!("  @ Code Gen: {} on {}", vrs.display(), os.display());

            let t_start = Instant::now();
            let ast = get_ast(vrs.display().to_string().as_str());
            let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
            println!("    - AST creation: {t_elapsed_ms} ms");

            let t_osspec = Instant::now();
            let osspec = get_osspec(os.display().to_string().as_str());
            let t_elapsed_ms = Instant::now().duration_since(t_osspec).as_millis();
            println!("    - OS Spec creation: {t_elapsed_ms} ms");

            let filename: String = vrs.file_stem().unwrap().to_str().unwrap().to_string();

            let t_start = Instant::now();
            let codegen = new_codegen_fn(outdir.as_path(), filename.clone());
            codegen.generate(&ast, &osspec);
            let t_elapsed_ms = Instant::now().duration_since(t_start).as_millis();
            println!("    - Code Gen: {t_elapsed_ms} ms");

            // run the compilation test
            if let Err(msg) = codegen.test_compile(&ast, &osspec) {
                println!("    - Compilation failed!");
                for l in msg.lines() {
                    println!("      > {l}")
                }
                // panic!("    - Compilation failed!");
            }

            outdir.pop();
        }
    }
}

#[test]
fn examples_codegen_c() {
    let codegen: CodeGenConstructor = |outdir, pkg| VelosiCodeGen::new_c(outdir, pkg);
    examples_codegen("c", codegen);
}

#[test]
fn examples_codegen_rust() {
    let codegen: CodeGenConstructor = |outdir, pkg| VelosiCodeGen::new_rust(outdir, pkg);
    examples_codegen("rust", codegen);
}
