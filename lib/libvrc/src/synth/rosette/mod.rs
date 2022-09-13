// Velosiraptor Code Generator
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

//! Synthesis Module: Rosette

// declare the modules
mod consts;
mod context;
mod expr;
mod fields;
mod grammar;
mod interface;
mod methods;
mod model;
mod resultparser;
mod state;
mod synth;

// external libraries
use std::fs;
use std::path::{Path, PathBuf};
use std::thread;

// rosette language library imports
use rosettelang::RosetteFile;

// the used libraries
use super::Operation;
use crate::ast::{AstNodeGeneric, AstRoot, Method, Segment};
use crate::synth::SynthError;

// re-exports
use resultparser::parse_result;

pub struct SynthRosette {
    outdir: PathBuf,
    _pkg: String,
}

impl SynthRosette {
    pub fn new(outdir: &Path, pkg: String) -> Self {
        SynthRosette {
            outdir: outdir.join(&pkg).join("synth"),
            _pkg: pkg,
        }
    }

    fn synth_create(&self, file: PathBuf, unit: &Segment, method: &Method) -> RosetteFile {
        let mut rkt = context::prepare_context(&unit.name, file);

        consts::add_consts(&mut rkt, unit);
        // adding state, interace and model
        state::add_state_def(&mut rkt, &unit.state);
        interface::add_interface_def(&mut rkt, &unit.interface);
        methods::add_methods(&mut rkt, &unit.methods);
        model::add_model_def(&mut rkt, &unit.state, &unit.interface);

        let m = unit.get_method("translate").unwrap();
        model::add_translate(&mut rkt, m);
        let m = unit.get_method("matchflags").unwrap();
        model::add_matchflags(&mut rkt, m);

        let state_syms = method.get_state_references();
        let state_bits = unit.state.referenced_field_bits(&state_syms);

        grammar::add_grammar(&mut rkt, &unit.interface, &state_syms, &state_bits);

        rkt
    }

    fn synth_map_part(&self, part: &str, unit: &Segment) -> RosetteFile {
        // create the context
        let rktfilepath = self.outdir.join(format!("{}_map_{}.rkt", unit.name, part));
        let m = unit.get_method(part).unwrap();

        let mut rkt = self.synth_create(rktfilepath, unit, m);

        let m = unit.get_method("map").unwrap();
        synth::add_synthesis(&mut rkt, part, unit, m);

        rkt.save();
        rkt
    }

    fn synth_unmap_part(&self, unit: &Segment) -> RosetteFile {
        // create the context
        let rktfilepath = self.outdir.join(format!("{}_unmap.rkt", unit.name));
        let m = unit.get_method("translate").unwrap();
        let mut rkt = self.synth_create(rktfilepath, unit, m);

        // let's pass in the map function here, as we want to invert it's effects
        let m = unit.get_method("map").unwrap();
        synth::add_synthesis(&mut rkt, "unmap", unit, m);

        rkt.save();
        rkt
    }

    /// synthesizes the `map` function and returns an ast of it
    pub fn synth_map(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        fs::create_dir_all(&self.outdir)?;

        for unit in &mut ast.segment_units_mut() {
            // translate part

            println!("synthesizing map: for {} in {:?}", unit.name, self.outdir);

            let mut rkt_translate = self.synth_map_part("translate", unit);
            let mut rkt_matchflags = self.synth_map_part("matchflags", unit);

            let translate_thread = thread::spawn(move || {
                println!("translate thread start!\n");
                let res_translate = rkt_translate.exec();
                println!("translate thread done: {}", res_translate);
                parse_result(&res_translate)
            });

            println!("matchflags thread start!\n");
            let res_matchflags = rkt_matchflags.exec();
            println!("matchflags thread done: {}", res_matchflags);

            let ops_matchflags = parse_result(&res_matchflags);
            let ops_translate = translate_thread.join().unwrap();

            let ops = Operation::merge(ops_matchflags, ops_translate);

            unit.map_ops = Some(ops);
        }

        Ok(())
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut &mut ast.segment_units_mut() {
            println!(
                "synthesizing unmap: for {} in {:?}",
                unit.name(),
                self.outdir
            );

            let mut rkt_translate = self.synth_unmap_part(unit);
            let res_translate = rkt_translate.exec();
            let ops_translate = parse_result(&res_translate);
            unit.unmap_ops = Some(ops_translate);
        }
        Ok(())
    }

    pub fn synth_protect(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            println!("synthesizing map: for {} in {:?}", unit.name(), self.outdir);
            let ops = Vec::new();
            unit.protect_ops = Some(ops);
        }

        Ok(())
    }

    pub fn synth_map_unmap_protect(&self, ast: &mut AstRoot) -> Result<(), SynthError> {
        self.synth_map(ast)?;
        self.synth_unmap(ast)?;
        self.synth_protect(ast)
    }
}
