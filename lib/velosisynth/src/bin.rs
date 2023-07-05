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

use std::collections::HashMap;
use std::env;
use std::io;
use std::io::Read;
use std::time::Instant;

use clap::{arg, command};
use simplelog::{ColorChoice, ConfigBuilder, LevelFilter, LevelPadding, TermLogger, TerminalMode};

use velosiast::{AstResult, VelosiAst, VelosiAstUnit};
use velosisynth::model;
use velosisynth::Z3SynthFactory;

pub fn main() {
    // get the command line argumentts
    let matches = command!() // requires `cargo` feature
        .arg(arg!(
            -v --verbose ... "Turn debugging verbosity on"
        ))
        .arg(arg!(-c --cores <VALUE>).default_value("num_cpu - 1"))
        .arg(arg!(-s --synth <VALUE>).default_value("all"))
        .arg(arg!(-u --unit <VALUE>).default_value("all"))
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
        .unwrap_or_else(|_| {
            std::thread::available_parallelism()
                .map(|i| i.into())
                .unwrap_or(1)
        });

    TermLogger::init(
        filter_level,
        config,
        TerminalMode::Stdout,
        ColorChoice::Auto,
    )
    .expect("failed to setup logger");

    let t_start = Instant::now();

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

    let t_parsing = Instant::now();

    let mut synthfactory = Z3SynthFactory::new();
    synthfactory.num_workers(ncores).default_log_dir();

    // TODO: might be able to put this in the ast and reuse it?
    let models = ast
        .segments()
        .iter()
        .map(|u| (u.ident().clone(), model::create(u, false)))
        .collect::<HashMap<_, _>>();

    let mut t_synth = Vec::new();
    for unit in ast.units_mut() {
        use std::rc::Rc;
        match unit {
            VelosiAstUnit::Segment(u) => {
                if u.is_abstract {
                    // don't handle abstract units
                    continue;
                }

                if let Some(unit_filter) = matches.get_one::<String>("unit").map(|s| s.as_str()) {
                    if !(unit_filter == "all" || unit_filter == u.ident().as_str()) {
                        continue;
                    }
                }

                let seg = Rc::get_mut(u);

                if seg.is_none() {
                    println!("could not obtain mutable reference to segment unit\n");
                    continue;
                }

                let seg = seg.unwrap();

                let mut t_synth_segment = Vec::new();

                t_synth_segment.push(("start", Instant::now()));

                let mut synth = synthfactory.create_segment(seg);

                t_synth_segment.push(("init", Instant::now()));

                synth.create_model();

                t_synth_segment.push(("Model Creation", Instant::now()));

                let sanity_check = synth.sanity_check();

                t_synth_segment.push(("Sanity Check", Instant::now()));

                if let Err(e) = sanity_check {
                    println!("{}", e);
                    log::error!(target: "main", "skipped synthesizing due to errors");
                    let stats = Some(synth.worker_pool_stats().clone());
                    t_synth.push((seg.ident_to_string(), t_synth_segment, Vec::new(), stats));
                    continue;
                }

                let mut synth_breakdown = Vec::new();
                let mem_model = matches.get_flag("mem-model");

                let stats = match matches.get_one::<String>("synth").map(|s| s.as_str()) {
                    Some("all") => {
                        println!("Synthesizing ALL for unit {}", synth.unit_ident());
                        synth.synthesize(mem_model);
                        synth_breakdown = vec![
                            ("map", synth.t_map_synthesis),
                            ("protect", synth.t_protect_synthesis),
                            ("unmap", synth.t_unmap_synthesis),
                        ];

                        let stats = synth.worker_pool_stats().clone();

                        match synth.finalize() {
                            Ok(p) => log::warn!(target: "main", "synthesis completed: {}", p),
                            Err(e) => log::error!(target: "main", "synthesis failed\n{}", e),
                        }
                        Some(stats)
                    }

                    Some("map") => {
                        println!("Synthesizing MAP for unit {}", synth.unit_ident());
                        match synth.synthesize_map(mem_model) {
                            Ok(p) => log::warn!(target: "main", "Program: {}", p),
                            Err(e) => log::error!(target: "main", "Synthesis failed:\n{}", e),
                        }
                        None
                    }

                    Some("unmap") => {
                        println!("Synthesizing UNMAP for unit {}", synth.unit_ident());
                        match synth.synthesize_unmap(mem_model) {
                            Ok(p) => log::warn!(target: "main", "Program: {}", p),
                            Err(e) => log::error!(target: "main", "Synthesis failed:\n{}", e),
                        }
                        None
                    }

                    Some("protect") => {
                        println!("Synthesizing PROTECT for unit {}", synth.unit_ident());
                        match synth.synthesize_protect(mem_model) {
                            Ok(p) => log::warn!(target: "main", "Program: {}", p),
                            Err(e) => log::error!(target: "main", "Synthesis failed:\n{}", e),
                        }
                        None
                    }
                    Some(x) => {
                        log::error!(target: "main", "unknown synth model '{}'", x);
                        return;
                    }
                    None => {
                        log::error!(target: "main", "synth mode not set");
                        return;
                    }
                };

                t_synth_segment.push(("Synthesis", Instant::now()));
                t_synth.push((
                    seg.ident_to_string(),
                    t_synth_segment,
                    synth_breakdown,
                    stats,
                ));
            }
            VelosiAstUnit::StaticMap(_s) => {
                // nothing to synthesize here
            }
            VelosiAstUnit::Enum(e) => {
                // try to differentiate enum variants
                let e = Rc::get_mut(e);

                if e.is_none() {
                    println!("could not obtain mutable reference to enum unit\n");
                    continue;
                }
                let e = e.unwrap();

                let mut synth = synthfactory.create_enum(e);
                synth.distinguish(&models);
            }
        }
    }

    let t_end = Instant::now();

    println!("=================================================================================");
    println!(
        "Total time               {:6} ms",
        t_end.duration_since(t_start).as_millis()
    );
    println!("=================================================================================");
    println!(
        "  Parsing time           {:6} ms",
        t_parsing.duration_since(t_start).as_millis()
    );

    if !t_synth.is_empty() {
        let t_synth_start = t_synth.first().unwrap().1.first().unwrap().1;
        let t_synth_end = t_synth.last().unwrap().1.last().unwrap().1;
        println!(
            "  Synthesis time         {:6} ms",
            t_synth_end.duration_since(t_synth_start).as_millis()
        );
        for (unit, t, breakdown, stats) in t_synth {
            println!(
                "---------------------------------------------------------------------------------"
            );
            let mut t_prev = t.first().unwrap().1;
            let t_last = t.last().unwrap().1;

            println!(
                "  {:20.20}   {:6} ms",
                unit,
                t_last.duration_since(t_prev).as_millis()
            );
            for (name, t) in t.iter().skip(1) {
                println!(
                    "   * {:17.17}   {:6} ms",
                    name,
                    t.duration_since(t_prev).as_millis()
                );
                t_prev = *t;
                if *name == "Synthesis" {
                    for (name, t) in breakdown.iter() {
                        println!("     - {:15.15}   {:6} ms", name, t.as_millis());
                    }
                }
            }
            if let Some(stats) = stats {
                println!("   - Synthesis Breakdown");
                println!("     - {:15.15}   {:6}", "num queries", stats.n_queries);
                println!("       {:15.15}   {:6}", " - cached", stats.n_cached);
                println!("     - {:15.15}   {:6} ms", "create", stats.t_create_ms);
                println!("     - {:15.15}   {:6} ms", "queued", stats.t_queued_ms);
                println!("     - {:15.15}   {:6} ms", "prepare", stats.t_prepare_ms);
                println!("     - {:15.15}   {:6} ms", "solver", stats.t_solver_ms);
            }
        }
    } else {
        println!("  Synthesis time         {:6} ms (not run due to error)", 0);
    }
    println!("=================================================================================\n");
}
