// Velosiraptor Synthesizer
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

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::thread;

use smt2::{Function, Smt2Context, Smt2File, SortedVar, Term, VarDecl};

use crate::ast::{AstNodeGeneric, AstRoot, Segment};
use crate::synth::SynthError;

mod consts;
mod expr;
mod field;
mod interface;
mod method;
mod model;
mod state;
mod task;
mod types;

pub struct SynthZ3 {
    outdir: PathBuf,
    _pkg: String,
}

impl SynthZ3 {
    pub fn new(outdir: &Path, pkg: String) -> Self {
        SynthZ3 {
            outdir: outdir.join(&pkg).join("synth"),
            _pkg: pkg,
        }
    }

    fn synth_create(&self, file: PathBuf, unit: &Segment) -> Smt2File {
        let mut z3file = smt2::Smt2File::new(file, String::new());

        consts::add_consts(z3file.get_context_mut(), unit);
        state::add_state_def(z3file.get_context_mut(), &unit.state);
        interface::add_interface_def(z3file.get_context_mut(), &unit.interface);
        model::add_model_def(z3file.get_context_mut(), &unit.state, &unit.interface);
        method::add_methods(z3file.get_context_mut(), &unit.methods);
        return z3file;
    }

    fn synth_map_part(&self, part: &str, unit: &Segment) -> Smt2File {
        // create the context
        let smtfile = self.outdir.join(format!("{}_map_{}.smt2", unit.name, part));
        let m = unit.get_method(part).unwrap();

        let mut smt = self.synth_create(smtfile, unit);
        let m = unit.get_method("map").unwrap();
        // synth::add_synthesis(&mut rkt, part, unit, m);
        smt
    }

    fn synth_unmap_part(&self, unit: &Segment) -> Smt2File {
        // create the context
        let smtfile = self.outdir.join(format!("{}_unmap.smt2", unit.name));
        let m = unit.get_method("translate").unwrap();

        let mut smt = self.synth_create(smtfile, unit);

        // let's pass in the map function here, as we want to invert it's effects
        let m = unit.get_method("map").unwrap();
        // synth::add_synthesis(&mut rkt, "unmap", unit, m);
        smt
    }

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        fs::create_dir_all(&self.outdir)?;
        for unit in &mut ast.segment_units_mut() {
            println!("synthesizing map: for {} in {:?}", unit.name(), self.outdir);

            // do the translate part
            let mut translate = self.synth_map_part("translate", unit);

            let t_fn = unit.get_method("translate").unwrap();
            method::add_translate_or_match_flags_fn(translate.get_context_mut(), t_fn);

            let m_fn = unit.get_method("map").unwrap();
            let mut smt = Smt2Context::new();

            // add the model state
            smt.section(String::from("Synthesis"));

            smt.subsection(String::from("State operations"));
            smt.variable(VarDecl::new(String::from("st!0"), String::from("Model_t")));

            // model::add_goal(&mut smt, m);

            let mut f = Function::new(String::from("map"), String::from("Model_t"));
            f.add_arg(String::from("st"), types::model());
            f.add_body(Term::fn_apply(
                String::from("Model.State.pte.present.set"),
                vec![Term::ident(String::from("st")), Term::num(1)],
            ));
            smt.function(f);

            let mut f = Function::new(String::from("assms"), types::boolean());
            f.add_arg(String::from("st"), types::model());
            f.add_arg(String::from("va"), types::num());
            f.add_body(Term::land(
                Term::bvlt(Term::ident(String::from("va")), Term::num(0x1000)),
                Term::bvge(Term::ident(String::from("va")), Term::num(0)),
            ));
            smt.function(f);

            smt.subsection(String::from("Verification"));
            smt.comment(String::from("TODO: operations to check"));

            let vars = vec![
                SortedVar::new(String::from("st!0"), String::from("Model_t")),
                SortedVar::new(String::from("va"), types::num()),
                SortedVar::new(String::from("size"), types::num()),
                SortedVar::new(String::from("flags"), types::flags()),
                SortedVar::new(String::from("pa"), types::num()),
            ];

            let term = Term::fn_apply(
                String::from("assms"),
                vec![
                    Term::ident(String::from("st!0")),
                    Term::ident(String::from("va")),
                ],
            )
            .implies(Term::fn_apply(
                String::from("translate.pre"),
                vec![
                    Term::fn_apply(String::from("map"), vec![Term::ident(String::from("st!0"))]),
                    Term::ident(String::from("va")),
                ],
            ));

            let t = Term::forall(vars, term);
            smt.assert(t);

            smt.check_sat();

            translate.extend_and_save(&smt);

            // do the match flags part
            let mut matchflags = self.synth_map_part("matchflags", unit);

            let t_fn = unit.get_method("matchflags").unwrap();
            method::add_translate_or_match_flags_fn(translate.get_context_mut(), t_fn);

            translate.save();
            let output = Command::new("z3")
                .args(["-smt2", translate.file().to_str().unwrap()])
                .output()
                .expect("failed to execute process");

            // grab the stdout
            let s = match String::from_utf8(output.stdout) {
                Ok(v) => v,
                Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
            };

            // if it's empty, assume error
            if s.is_empty() {
                let e = match String::from_utf8(output.stderr) {
                    Ok(v) => v,
                    Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
                };
            }

            println!("smt output:\n\n{}\n\n", s);

            // let translate_thread = thread::spawn(move || {
            //     println!("translate thread start!\n");
            //     translate.save();

            //     let output = Command::new("z3")
            //         .args(["-smt2", translate.file().to_str().unwrap()])
            //         .output()
            //         .expect("failed to execute process");

            //     // grab the stdout
            //     let s = match String::from_utf8(output.stdout) {
            //         Ok(v) => v,
            //         Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
            //     };

            //     // if it's empty, assume error
            //     if s.is_empty() {
            //         let e = match String::from_utf8(output.stderr) {
            //             Ok(v) => v,
            //             Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
            //         };
            //         println!("rosette failure!");
            //         println!("{}", e);
            //     }

            //     //println!("translate thread done: {}", res_translate);
            //     //parse_result(&res_translate)
            // });

            // matchflags.save();

            // translate_thread.join().unwrap();

            let ops = Vec::new();
            unit.map_ops = Some(ops);
        }

        Ok(())
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        fs::create_dir_all(&self.outdir)?;
        for unit in &mut ast.segment_units_mut() {
            println!(
                "synthesizing unmap: for {} in {:?}",
                unit.name(),
                self.outdir
            );

            let mut translate = self.synth_unmap_part(unit);

            // spin off multi threaded synthesis...
            translate.save();

            let ops = Vec::new();
            unit.map_ops = Some(ops);
        }

        Ok(())
    }

    pub fn synth_protect(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        fs::create_dir_all(&self.outdir)?;
        for unit in &mut ast.segment_units_mut() {
            println!(
                "synthesizing protect: for {} in {:?}",
                unit.name(),
                self.outdir
            );
            let ops = Vec::new();
            unit.protect_ops = Some(ops);
        }
        Ok(())
    }
}
