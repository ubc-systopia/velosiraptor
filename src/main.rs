// Velosiraptor Lexer
//
//
// MIT License
//
// Copyright (c) 2021 Systopia Lab, Computer Science, University of British Columbia
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

//! Velosiraptor Compiler

use std::sync::Arc;
use std::{fmt::Display, rc::Rc};

use clap::{Parser, ValueEnum};
use colored::*;
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, LevelPadding, TermLogger, TerminalMode};

use std::path::Path;
use std::process::exit;

// get the parser module
use velosiast::{AstResult, VelosiAst, VelosiAstUnit};
use velosicodegen::VelosiCodeGen;
use velosisynth::{create_models, Z3SynthFactory};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// the input file to operate on
    infile: Option<String>,

    /// output directory where to emit generated files
    #[arg(short, long)]
    outdir: Option<String>,

    /// name of the compilation unit
    #[arg(short, long, default_value_t = String::from("mympu"))]
    name: String,

    /// the number of cores used for synthesis
    #[arg(short, long, default_value_t = 1)]
    parallelism: usize,

    /// treat warnings as errors
    #[arg(short, long, default_value_t = false)]
    werror: bool,

    /// log all smt queries sent to Z3
    #[arg(short, long, default_value_t = false)]
    logsmt: bool,

    /// language of the generated code
    #[arg(value_enum, default_value_t = Platform::ArmFastModels)]
    platform: Platform,

    /// language of the generated code
    #[arg(value_enum, default_value_t = OutputLanguage::C)]
    language: OutputLanguage,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,

    /// Synthesize using the abstract memory model
    #[arg(short, long, default_value_t = false)]
    mem_model: bool,
}

/// defines the output language for the generate code
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum OutputLanguage {
    /// emit C code
    C,
    /// emit Rust code
    Rust,
}

impl Display for OutputLanguage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputLanguage::C => write!(f, "C"),
            OutputLanguage::Rust => write!(f, "Rust"),
        }
    }
}

/// the platform to generate hardware component for
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Platform {
    /// generate hardware component for the Arm FastModels platform
    ArmFastModels,
}

impl Display for Platform {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Platform::ArmFastModels => write!(f, "ArmFastModels"),
        }
    }
}

// use libvrc::error::{ErrorLocation, VrsError};
// fn print_errors_and_exit<I: ErrorLocation + std::fmt::Display>(
//     msg: &str,
//     err: VrsError<I>,
//     target: &str,
//     cnt: Issues,
// ) {
//     err.print();
//     eprintln!("{}{}{}.\n", "error".bold().red(), ": ".bold(), msg.bold());
//     abort(target, cnt)
// }

// fn abort(target: &str, cnt: Issues) {
//     let msg = format!(": aborting due to previous {} error(s)", cnt.errors);
//     eprint!("{}{}", "error".bold().red(), msg.bold());
//     if cnt.warnings > 0 {
//         let msg = format!(", and {} warnings emitted", cnt.warnings);
//         eprintln!("{}\n", msg.bold());
//     } else {
//         eprintln!(); // add some newline
//     }
//     eprintln!(
//         "{}: could not compile `{}`.\n",
//         "error".bold().red(),
//         target
//     );
//     exit(-1);
// }

/// Main - entry point into the application
fn main() {
    // parse command line arguments
    let cli = Cli::parse();

    // setting the log level
    let filter_level = match cli.verbose {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    // initialize the logger
    let config = ConfigBuilder::default()
        .set_level_padding(LevelPadding::Right)
        .set_thread_level(LevelFilter::Off)
        .set_target_level(LevelFilter::Warn)
        .set_location_level(LevelFilter::Off)
        .build();

    TermLogger::init(
        filter_level,
        config,
        TerminalMode::Stdout,
        ColorChoice::Auto,
    )
    .expect("failed to setup logger");

    // print the start message
    eprintln!(
        "{:>8}: Velosiraptor Compiler (vrc)...\n",
        "start".bold().green(),
    );

    log::info!("Info output enabled");
    log::debug!("Debug output enabled");
    log::trace!("Tracing output enabled");

    log::info!("---------------------------------------------------------------------------------");

    log::info!(
        "Input file: {}",
        cli.infile.as_ref().unwrap_or(&String::from("--"))
    );
    log::info!(
        "Output directory: {}",
        cli.outdir.as_ref().unwrap_or(&String::from("--"))
    );
    log::info!("Compilation unit name: {}", cli.name);
    log::info!("Parallelism: {}", cli.parallelism);
    log::info!("Warnings as errors: {}", cli.werror);
    log::info!("Log SMT queries: {}", cli.logsmt);
    log::info!("Output language: {}", cli.language);
    log::info!("Platform: {}", cli.platform);
    log::info!("Verbosity: {}", cli.verbose);

    log::info!("---------------------------------------------------------------------------------");

    let infile = if let Some(infile) = cli.infile.as_deref() {
        infile
    } else {
        eprintln!("{}: no input file specified.\n", "error".bold().red(),);
        exit(-1);
    };

    // ===========================================================================================
    // Step 1: Parse the input file
    // ===========================================================================================

    eprintln!("{:>8}: {}...\n", "parse".bold().green(), infile);

    // let's try to create a file parser
    let mut ast = match VelosiAst::from_file(infile) {
        AstResult::Ok(ast) => ast,
        AstResult::Issues(ast, err) => {
            if !cli.werror {
                ast
            } else {
                eprintln!(
                    "{}: could not compile `{}`.\n",
                    "error".bold().red(),
                    infile.bold()
                );
                eprint!(
                    "{}{}",
                    "error".bold().red(),
                    "compilation failed due to errors (Werror)".bold()
                );
                println!("{err}");
                exit(-1);
            }
        }
        AstResult::Err(err) => {
            eprintln!(
                "{}: could not compile `{}`.\n",
                "error".bold().red(),
                infile.bold()
            );
            println!("{err}");
            exit(-1);
        }
    };

    log::debug!("AST:");
    log::debug!("----------------------------");
    log::debug!("{}", ast);
    log::debug!("----------------------------");

    // ===========================================================================================
    // Step 2: Synthesis
    // ===========================================================================================

    // if there is no outdir specified we won't do anything
    let outpath = if let Some(outpath) = cli.outdir.as_deref() {
        Path::new(outpath)
    } else {
        eprintln!(
            "{:>8}: skipping code generation and synthesis (no outdir specified).\n",
            "synth".bold().green(),
        );
        exit(0);
    };

    if outpath.exists() && !outpath.is_dir() {
        eprintln!(
            "{}{} `{}`.\n",
            "error".bold().red(),
            ": output path exists, but s not a directory: ".bold(),
            outpath.display()
        );
        exit(-1);
    }

    eprintln!("{:>8}: {}...\n", "synth".bold().green(), infile);

    let synth_path = Arc::new(outpath.join("synth"));

    let mut synthfactory = Z3SynthFactory::new();
    synthfactory
        .logdir(synth_path)
        .logging(cli.logsmt)
        .num_workers(cli.parallelism);

    let models = create_models(&ast);
    for unit in ast.units_mut() {
        match unit {
            VelosiAstUnit::Segment(u) => {
                if u.is_abstract {
                    // don't do anythign with abstract segments
                    continue;
                }

                let seg = Rc::get_mut(u);
                if seg.is_none() {
                    eprintln!(
                        "{}{}.\n",
                        "error".bold().red(),
                        ": could not obtain mutable reference".bold()
                    );
                    exit(-1);
                }

                let seg = seg.unwrap();
                let mut synth = synthfactory.create_segment(seg, models[seg.ident()].clone());

                if let Err(_e) = synth.sanity_check() {
                    eprintln!(
                        "{}{}.\n",
                        "error".bold().red(),
                        ": model sanity check has failed".bold()
                    );
                    exit(-1);
                }

                println!("Synthesizing ALL for unit {}", synth.unit_ident());
                synth.synthesize(cli.mem_model);

                match synth.finalize() {
                    Ok(p) => log::warn!(target: "main", "synthesis completed: {}", p),
                    Err(_e) => {
                        eprintln!(
                            "{}{}.\n",
                            "error".bold().red(),
                            ": synthesis has failed".bold(),
                        );
                        exit(-1);
                    }
                }
            }
            VelosiAstUnit::OSSpec(_) | VelosiAstUnit::StaticMap(_) => {
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
        }
    }

    // ===========================================================================================
    // Step 3: Code Generation
    // ===========================================================================================

    eprintln!("{:>8}: {}...\n", "codegen".bold().green(), infile);

    let code_path = Arc::new(outpath.join("code"));

    let codegen = match cli.language {
        OutputLanguage::C => VelosiCodeGen::new_c(&code_path, cli.name.clone()),
        OutputLanguage::Rust => VelosiCodeGen::new_rust(&code_path, cli.name.clone()),
    };

    if let Err(_e) = codegen.generate(&ast) {
        eprintln!(
            "{}{}.\n",
            "error".bold().red(),
            ": code generation failed".bold(),
        );
        exit(-1);
    }

    // let codegen = match backend {
    //     "rust" => CodeGen::new_rust(outpath, pkgname.clone()),
    //     "c" => CodeGen::new_c(outpath, pkgname.clone()),
    //     s => {
    //         eprintln!(
    //             "{}{} `{}`.\n",
    //             "error".bold().red(),
    //             ": unsupported code backend".bold(),
    //             s.bold()
    //         );
    //         abort(infile, issues);
    //         return;
    //     }
    // };

    // ===========================================================================================
    // Step 4: Hardware Generation
    // ===========================================================================================

    eprintln!("{:>8}: {}...\n", "hwgen".bold().green(), infile);

    // // ===========================================================================================
    // // Step 6: Generate OS code
    // // ===========================================================================================

    // log::info!("==== CODE GENERATION STAGE ====");

    // // so things should be fine, we can now go and generate stuff

    // // generate the raw interface files: this is the "language" to interface

    // codegen.prepare().unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during codegen preparation generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    // });

    // // generate the raw interface files: this is the "language" to interface
    // eprintln!(
    //     "{:>8}: generating interface files...\n",
    //     "generate".bold().green(),
    // );

    // codegen.generate_globals(&ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during globals generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    // });

    // codegen.generate_interface(&ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during interface generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    // });

    // // synthsizer.synth_map_unmap_protect(&mut ast).unwrap_or_else(|e| {
    // //     eprintln!(
    // //         "{}{} `{}`.\n",
    // //         "error".bold().red(),
    // //         ": failure during interface generation".bold(),
    // //         e
    // //     );
    // //     abort(infile, issues);
    // //     panic!("s");
    // // });

    // // generate the unit files that use the interface files
    // eprintln!(
    //     "{:>8}: synthesizing map function...\n",
    //     "synthesis".bold().green(),
    // );

    // synthsizer.synth_map(&mut ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during interface generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    //     panic!("s");
    // });

    // eprintln!(
    //     "{:>8}: synthesizing unmap function...\n",
    //     "synthesis".bold().green(),
    // );

    // synthsizer.synth_unmap(&mut ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during interface generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    //     panic!("s");
    // });

    // eprintln!(
    //     "{:>8}: synthesizing prot function...\n",
    //     "synthesis".bold().green(),
    // );

    // synthsizer.synth_protect(&mut ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during interface generation".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    //     panic!("s");
    // });

    // // generate the unit files that use the interface files
    // eprintln!(
    //     "{:>8}: generating unit files...\n",
    //     "generate".bold().green(),
    // );

    // codegen.generate_units(&ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during unit generation".bold(),
    //         e
    //     );
    // });

    // codegen.finalize(&ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during code generation finalization".bold(),
    //         e
    //     );
    //     abort(infile, issues);
    // });

    // // ===========================================================================================
    // // Step 6: Generate simulator modules
    // // ===========================================================================================

    // log::info!("==== HARDWARE GENERATION STAGE ====");

    // // we can generate some modules
    // let outpath = Path::new(outdir);

    // if outpath.exists() && !outpath.is_dir() {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": output path exists, but s not a directory: ".bold(),
    //         outdir.bold()
    //     );
    //     abort(infile, issues);
    //     return;
    // }

    // eprintln!(
    //     "{:>8}: prepare for hardware generation {}...\n",
    //     "generate".bold().green(),
    //     platform
    // );

    // let platform = match platform {
    //     "fastmodels" => HWGen::new_fastmodels(outpath, pkgname),
    //     s => {
    //         eprintln!(
    //             "{}{} `{}`.\n",
    //             "error".bold().red(),
    //             ": unsupported platform backend".bold(),
    //             s.bold()
    //         );
    //         abort(infile, issues);
    //         return;
    //     }
    // };

    // platform.prepare().unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during hw platform preparation".bold(),
    //         e
    //     );
    // });

    // eprintln!(
    //     "{:>8}: generate hardware component...\n",
    //     "generate".bold().green(),
    // );

    // platform.generate(&ast).unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during hw platform generation".bold(),
    //         e
    //     );
    // });

    // eprintln!(
    //     "{:>8}: finalize hardware component...\n",
    //     "generate".bold().green(),
    // );

    // platform.finalize().unwrap_or_else(|e| {
    //     eprintln!(
    //         "{}{} `{}`.\n",
    //         "error".bold().red(),
    //         ": failure during hw platform finalization".bold(),
    //         e
    //     );
    // });

    // if issues.warnings > 0 {
    //     let msg = format!("{} warning(s) emitted", issues.warnings);
    //     eprintln!("{}{}.\n", "warning: ".bold().yellow(), msg.bold());
    // }

    // // ok all done.
    eprintln!("{:>8}: ...\n", "finished".bold().green());
}
