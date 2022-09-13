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

use smt2::{Smt2Context, Smt2File};

use crate::ast::{AstNodeGeneric, AstRoot, Segment};
use crate::synth::SynthError;

use self::query::Z3Query;
use self::worker::Z3WorkerPool;

mod consts;
mod expr;
mod field;
mod instance;
mod interface;
mod method;
mod model;
mod operations;
mod query;
mod state;
mod types;
mod worker;

pub struct SynthZ3 {
    outdir: PathBuf,
    _pkg: String,
    parallelism: usize,
    workerpool: Z3WorkerPool,
}

impl SynthZ3 {
    pub fn new(outdir: &Path, pkg: String, parallelism: usize) -> Self {
        let outdir = outdir.join(&pkg).join("synth");
        fs::create_dir_all(&outdir).expect("Failed to create synth directory");

        let mut workerpool = if parallelism > 0 {
            Z3WorkerPool::with_num_workers(parallelism, Some(&outdir))
        } else {
            Z3WorkerPool::new(Some(&outdir))
        };

        println!("Synthesizing with Z3");

        SynthZ3 {
            outdir,
            _pkg: pkg,
            parallelism,
            workerpool,
        }
    }

    pub fn terminate(&mut self) {
        self.workerpool.terminate();
    }

    fn create_unit_context(&self, unit: &Segment) -> Smt2Context {
        let mut smt = Smt2Context::with_default_options();

        // general definitions

        types::add_type_defs(&mut smt, unit.inbitwidth, unit.outbitwidth);

        // stuff
        consts::add_consts(&mut smt, unit);
        state::add_state_def(&mut smt, &unit.state);
        interface::add_interface_def(&mut smt, &unit.interface);
        model::add_model_def(&mut smt, &unit);
        method::add_methods(&mut smt, &unit.methods);

        smt.section(String::from("Translate and Matchflags"));
        let t_fn = unit.get_method("translate").unwrap();
        method::add_translate_or_match_flags_fn(&mut smt, t_fn);
        method::add_translate_result_check(&mut smt, t_fn);

        let t_fn = unit.get_method("matchflags").unwrap();
        method::add_translate_or_match_flags_fn(&mut smt, t_fn);

        smt
    }

    fn synth_create(&mut self, file: PathBuf, unit: &Segment) -> Smt2File {
        let mut z3file = smt2::Smt2File::new(file, String::new());

        types::add_type_defs(z3file.as_context_mut(), unit.inbitwidth, unit.outbitwidth);
        consts::add_consts(z3file.as_context_mut(), unit);
        state::add_state_def(z3file.as_context_mut(), &unit.state);
        interface::add_interface_def(z3file.as_context_mut(), &unit.interface);
        model::add_model_def(z3file.as_context_mut(), unit);
        method::add_methods(z3file.as_context_mut(), &unit.methods);

        z3file
    }

    fn synth_map_part(&mut self, part: &str, unit: &Segment) -> Smt2File {
        // create the context
        let smtfile = self.outdir.join(format!("{}_map_{}.smt2", unit.name, part));
        let _m = unit.get_method(part).unwrap();

        let smt = self.synth_create(smtfile, unit);
        let _m = unit.get_method("map").unwrap();
        // synth::add_synthesis(&mut rkt, part, unit, m);
        smt
    }

    fn add_synth_map_tasks(&mut self, _unit: &mut Segment) {}

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            println!("synthesizing map: for {} in {:?}", unit.name(), self.outdir);
            // create the base unit context that provides the framework for synthesis
            let ctx = self.create_unit_context(unit);

            // perform worker reset and init with the given context
            self.workerpool.reset_with_context(Z3Query::from(ctx));

            self.add_synth_map_tasks(unit);
        }

        return Ok(());

        // let _m_fn = unit.get_method("map").unwrap();
        // let mut smt = Smt2Context::new();

        // smt.subsection(String::from("State operations"));
        // smt.variable(VarDecl::new(String::from("st!0"), String::from("Model_t")));

        // // model::add_goal(&mut smt, m);

        // let mut f = Function::new(String::from("map"), String::from("Model_t"));
        // f.add_arg(String::from("st"), types::model());
        // f.add_body(Term::fn_apply(
        //     String::from("Model.State.pte.present.set"),
        //     vec![Term::ident(String::from("st")), Term::num(1)],
        // ));
        // smt.function(f);

        // let mut f = Function::new(String::from("assms"), types::boolean());
        // f.add_arg(String::from("st"), types::model());
        // f.add_arg(String::from("va"), types::num());
        // f.add_body(Term::land(
        //     Term::bvlt(Term::ident(String::from("va")), Term::num(0x1000)),
        //     Term::bvge(Term::ident(String::from("va")), Term::num(0)),
        // ));
        // smt.function(f);

        // smt.subsection(String::from("Verification"));
        // smt.comment(String::from("TODO: operations to check"));

        // let vars = vec![
        //     SortedVar::new(String::from("st!0"), String::from("Model_t")),
        //     SortedVar::new(String::from("va"), types::num()),
        //     SortedVar::new(String::from("size"), types::num()),
        //     SortedVar::new(String::from("flags"), types::flags()),
        //     SortedVar::new(String::from("pa"), types::num()),
        // ];

        // let term = Term::fn_apply(
        //     String::from("assms"),
        //     vec![
        //         Term::ident(String::from("st!0")),
        //         Term::ident(String::from("va")),
        //     ],
        // )
        // .implies(Term::fn_apply(
        //     String::from("translate.pre"),
        //     vec![
        //         Term::fn_apply(String::from("map"), vec![Term::ident(String::from("st!0"))]),
        //         Term::ident(String::from("va")),
        //     ],
        // ));

        // let t = Term::forall(vars, term);
        // smt.assert(t);

        // smt.check_sat();

        // let mut w = worker::Z3Worker::new(1);

        // let t = worker::Z3Task::from(translate);
        // w.send_task(t);
        // if let Some(r) = w.recv_result() {
        //     println!("Got result: {}", r.result);
        // } else {
        //     panic!("no result");
        // }

        // let t = worker::Z3Task::from(smt);
        // w.send_task(t);

        // if let Some(r) = w.recv_result() {
        //     println!("Got result: {}", r.result);
        // } else {
        //     panic!("no result");
        // }

        // do the match flags part
        // let matchflags = self.synth_map_part("matchflags", unit);

        // let t_fn = unit.get_method("matchflags").unwrap();
        // method::add_translate_or_match_flags_fn(translate.as_context_mut(), t_fn);

        // translate.save();
        // let output = Command::new("z3")
        //     .args(["-smt2", translate.file().to_str().unwrap()])
        //     .output()
        //     .expect("failed to execute process");

        // // grab the stdout
        // let s = match String::from_utf8(output.stdout) {
        //     Ok(v) => v,
        //     Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        // };

        // // if it's empty, assume error
        // if s.is_empty() {
        //     let e = match String::from_utf8(output.stderr) {
        //         Ok(v) => v,
        //         Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
        //     };
        // }

        // println!("smt output:\n\n{}\n\n", s);

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

        //     let ops = Vec::new();
        //     unit.map_ops = Some(ops);
        // }
    }

    fn synth_unmap_part(&mut self, unit: &Segment) -> Smt2File {
        // create the context
        let smtfile = self.outdir.join(format!("{}_unmap.smt2", unit.name));
        let _m = unit.get_method("translate").unwrap();

        let smt = self.synth_create(smtfile, unit);

        // let's pass in the map function here, as we want to invert it's effects
        let _m = unit.get_method("map").unwrap();
        // synth::add_synthesis(&mut rkt, "unmap", unit, m);
        smt
    }

    fn add_synth_unmap_tasks(&mut self, unit: &Segment) {
        let translate = self.synth_unmap_part(unit);

        // spin off multi threaded synthesis...
        translate.save();
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            println!(
                "synthesizing unmap: for {} in {:?}",
                unit.name(),
                self.outdir
            );

            // create the base unit context that provides the framework for synthesis
            let ctx = self.create_unit_context(unit);

            // perform worker reset and init with the given context
            self.workerpool.reset_with_context(Z3Query::from(ctx));

            self.add_synth_unmap_tasks(unit);

            let ops = Vec::new();
            unit.unmap_ops = Some(ops);
        }

        Ok(())
    }

    fn add_synth_protect_tasks(&mut self, _unit: &mut Segment) {}

    pub fn synth_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            println!(
                "synthesizing protect: for {} in {:?}",
                unit.name(),
                self.outdir
            );

            // create the base unit context that provides the framework for synthesis
            let ctx = self.create_unit_context(unit);

            // perform worker reset and init with the given context
            self.workerpool.reset_with_context(Z3Query::from(ctx));

            self.add_synth_protect_tasks(unit);

            // perform search

            let ops = Vec::new();
            unit.protect_ops = Some(ops);
        }

        Ok(())
    }

    pub fn synth_map_unmap_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            let ctx = self.create_unit_context(unit);
            self.workerpool.reset_with_context(Z3Query::from(ctx));

            self.add_synth_protect_tasks(unit);
            self.add_synth_unmap_tasks(unit);
            self.add_synth_map_tasks(unit);

            // do stuff
        }
        Ok(())
    }
}
