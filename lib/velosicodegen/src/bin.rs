// Velosilexer -- a lexer for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiLexer -- The Velosiraptor Lexer Example Programm
//!
//! This example program

use std::env;
use std::io;
use std::io::Read;
use std::path::Path;
use std::time::Instant;

use clap::{arg, command, Arg, ArgAction};
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, LevelPadding, TermLogger, TerminalMode};

use velosiast::{AstResult, VelosiAst, VelosiAstUnit};
use velosicodegen::VelosiCodeGen;
use velosisynth::create_models;
use velosisynth::Z3SynthFactory;

pub fn main() {
    // get the command line argumentts
    let matches = command!() // requires `cargo` feature
        .arg(arg!(
            -v --verbose ... "Turn debugging verbosity on"
        ))
        .arg(arg!(-c --cores <VALUE>).default_value("1"))
        .arg(
            Arg::new("nosynth")
                .short('n')
                .long("no-synth")
                .action(ArgAction::SetTrue),
        )
        .arg(arg!(-o --output <VALUE>).default_value("out"))
        .arg(arg!(-l --lang <VALUE>).default_value("c"))
        .arg(arg!(-p --pkg <VALUE>).default_value("myunit"))
        .arg(arg!(-t --target <VALUE>).default_value("none"))
        .arg(arg!(
            -m --"mem-model" "Synthesize using the abstract memory model"
        ))
        .arg(arg!([fname] "Optional name to operate on"))
        .get_matches();

    let filter_level = match matches
        .get_one::<u8>("verbose")
        .expect("Count's are defaulted")
    {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    let config = ConfigBuilder::default()
        .set_level_padding(LevelPadding::Right)
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Warn)
        .set_location_level(LevelFilter::Off)
        .build();

    let ncores = matches
        .get_one::<String>("cores")
        .unwrap()
        .parse::<usize>()
        .unwrap();

    let no_synth = matches.get_flag("nosynth");

    TermLogger::init(
        filter_level,
        config,
        TerminalMode::Stdout,
        ColorChoice::Auto,
    )
    .expect("failed to setup logger");

    let _t_start = Instant::now();

    let pgk = matches.get_one::<String>("pkg").unwrap();
    let path = Path::new(matches.get_one::<String>("output").unwrap());

    let codegen = match matches.get_one::<String>("lang") {
        Some(cd) => match cd.as_str() {
            "c" => VelosiCodeGen::new_c(path, pgk.to_string()),
            "rust" => VelosiCodeGen::new_rust(path, pgk.to_string()),
            _ => {
                log::error!(target: "main", "unsupported language specified");
                return;
            }
        },
        None => {
            log::error!(target: "main", "no language specified");
            return;
        }
    };

    let ast = match matches.get_one::<String>("fname") {
        Some(filename) => VelosiAst::from_file(filename),
        None => {
            let mut buffer = String::new();
            let mut stdin = io::stdin();
            stdin
                .read_to_string(&mut buffer)
                .expect("could not read from stdin");
            VelosiAst::from_string(buffer)
        }
    };

    let mut ast = match ast {
        AstResult::Ok(ast) => {
            // println!("{}", ast);
            ast
        }
        AstResult::Issues(ast, err) => {
            // println!("{}", ast);
            println!("{}", err);
            ast
        }
        AstResult::Err(err) => {
            println!("{}", err);
            return;
        }
    };

    let target = match matches.get_one::<&str>("target") {
        None | Some(&"none") => VelosiAst::default(),
        Some(f) => {
            match VelosiAst::from_file(f) {
                AstResult::Ok(ast) => {
                    // println!("{}", ast);
                    ast
                }
                AstResult::Issues(ast, err) => {
                    // println!("{}", ast);
                    println!("{}", err);
                    ast
                }
                AstResult::Err(err) => {
                    println!("{}", err);
                    return;
                }
            }
        }
    };

    if !no_synth {
        let mut synthfactory = Z3SynthFactory::new();
        synthfactory.num_workers(ncores).default_log_dir();
        let models = create_models(&ast);

        for unit in ast.units_mut() {
            use std::rc::Rc;
            match unit {
                VelosiAstUnit::Segment(u) => {
                    if u.is_abstract {
                        // don't do anythign with abstract segments
                        continue;
                    }

                    let seg = Rc::get_mut(u);

                    if seg.is_none() {
                        println!("could not obtain mutable reference to segment unit\n");
                        continue;
                    }

                    let seg = seg.unwrap();

                    let mut t_synth_segment = Vec::new();

                    t_synth_segment.push(("start", Instant::now()));

                    let mut synth = synthfactory.create_segment(seg, models[seg.ident()].clone());

                    let sanity_check = synth.sanity_check();

                    t_synth_segment.push(("Sanity Check", Instant::now()));

                    if let Err(e) = sanity_check {
                        println!("{}", e);
                        log::error!(target: "main", "skipped synthesizing due to errors");
                        continue;
                    }

                    println!("Synthesizing ALL for unit {}", synth.unit_ident());
                    synth.synthesize(matches.get_flag("mem-model"));
                    match synth.finalize() {
                        Ok(p) => log::warn!(target: "main", "synthesis completed: {}", p),
                        Err(e) => log::error!(target: "main", "synthesis failed\n{}", e),
                    }
                }
                VelosiAstUnit::StaticMap(_s) => {
                    // nothing to synthesize here
                }
                VelosiAstUnit::Enum(e) => {
                    // try to differentiate enum variants
                    println!("Checking distinguishability for enum {}", e.ident());
                    let e = Rc::get_mut(e);

                    if e.is_none() {
                        println!("could not obtain mutable reference to enum unit\n");
                        continue;
                    }
                    let e = e.unwrap();

                    let mut synth = synthfactory.create_enum(e);
                    match synth.distinguish(&models) {
                        Ok(()) => {
                            log::info!(target: "main", "the variants of {} are distinguishable", e.ident())
                        }
                        Err(e) => log::error!(target: "main", "Distinguishing failed:\n{}", e),
                    }
                }
                VelosiAstUnit::OSSpec(_) => {
                    // nothing here
                }
            }
        }
    }

    if let Err(e) = codegen.generate(&ast, &target) {
        log::error!(target: "main", "code generation failed\n{:?}", e);
    }
}
