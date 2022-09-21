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

use smt2::{Smt2Context, Smt2File, Smt2Option, SortedVar, Term, VarDecl};

use crate::ast::{AstNodeGeneric, AstRoot, Expr, Method, Segment};
use crate::error::VrsError;
use crate::synth::SynthError;

use self::operations::Program;
use self::query::{Z3Query, Z3Result, Z3Ticket};
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

        let workerpool = if parallelism > 0 {
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
        let mut smt = Smt2Context::new();

        // options
        smt.set_option(Smt2Option::ProduceUnsatCores(true));

        // general definitions

        types::add_type_defs(&mut smt, unit.inbitwidth, unit.outbitwidth);

        // stuff
        consts::add_consts(&mut smt, unit);
        state::add_state_def(&mut smt, &unit.state);
        interface::add_interface_def(&mut smt, &unit.interface);
        model::add_model_def(&mut smt, &unit);
        method::add_methods(&mut smt, &unit.methods);

        smt.section(String::from("Translate and Matchflags"));
        let m = unit.get_method("translate").unwrap();
        method::add_translate_or_match_flags_fn(&mut smt, m);
        method::add_translate_result_check(&mut smt, m);

        let m = unit.get_method("matchflags").unwrap();
        method::add_translate_or_match_flags_fn(&mut smt, m);

        let m = unit.get_method("map").unwrap();
        method::add_map_unmap_protect_assms(&mut smt, m);

        let m = unit.get_method("unmap").unwrap();
        method::add_map_unmap_protect_assms(&mut smt, m);

        let m = unit.get_method("protect").unwrap();
        method::add_map_unmap_protect_assms(&mut smt, m);

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

    fn add_requires_tasks(&mut self, unit: &Segment, m: &Method) {}

    fn add_synth_map_translate_tasks(&mut self, unit: &mut Segment) {
        // get the map functions
        let m_fn = unit.get_method("map").unwrap();
        // get the translate function
        let t_fn = unit.get_method("translate").unwrap();
    }

    // fn add_synth_map_matchflags_tasks(&mut self, unit: &mut Segment) {
    //     // get the map functions
    //     let m_fn = unit.get_method("map").unwrap();
    //     // get the translate function
    //     let t_fn = unit.get_method("matchflags").unwrap();

    //     /* preconditions */
    // }

    fn add_check_for_precondition(
        &mut self,
        m_fn: &Method,
        progs: &mut Vec<Program>,
    ) -> Vec<Z3Ticket> {
        for (i, prog) in progs.drain(..).enumerate() {
            println!("____ PROGRAM");

            let (mut smt, symvars) = prog.to_smt2("map", m_fn.args.as_slice());

            let mut vars = vec![SortedVar::new(
                String::from("st!0"),
                String::from("Model_t"),
            )];
            for a in &m_fn.args {
                vars.push(SortedVar::new(
                    a.name.clone(),
                    types::type_to_smt2(&a.ptype),
                ));
            }

            let pre = Term::fn_apply(
                String::from("translate.assms"),
                vec![
                    Term::ident(String::from("st!0")),
                    Term::ident(String::from("va")),
                ],
            );

            let mut map_fn_args = vec![Term::ident(String::from("st!0"))];
            for v in m_fn.args.iter() {
                map_fn_args.push(Term::ident(v.name.clone()));
            }

            let check = Term::fn_apply(
                String::from("translate.pre"),
                vec![
                    Term::fn_apply(String::from("map"), map_fn_args),
                    Term::ident(String::from("va")),
                ],
            );

            let t = Term::forall(vars, pre.implies(check));

            smt.assert(t);
            smt.check_sat();

            symvars.add_get_values(&mut smt);

            let mut smtctx = Smt2Context::new();
            smtctx.subsection(String::from("Verification"));
            smtctx.level(smt);

            let mut query = Z3Query::from(smtctx);
            query.set_program(prog);

            match self.workerpool.submit_query(query) {
                Ok(t) => {
                    println!("Submitted query: {}", t);
                }
                Err(e) => {
                    println!("Failed to submit query.");
                }
            }
        }
        Vec::new()
    }

    fn check_precondition_satisfiability(&mut self, m_fn: &Method, t_fn: &Method, f_fn: &Method) {
        let mut smt = Smt2Context::new();

        // declare a variable for each
        smt.variable(VarDecl::new(String::from("st"), String::from("Model_t")));

        for a in &m_fn.args {
            smt.variable(VarDecl::new(a.name.clone(), types::type_to_smt2(&a.ptype)));
        }

        for (i, p) in f_fn.requires.iter().enumerate() {
            smt.comment(format!("{}: {}", m_fn.name, p));
            let name = format!("f_fn-{}", i);
            smt.assert(Term::named(expr::expr_to_smt2(p, "st"), name));
        }

        for (i, p) in t_fn.requires.iter().enumerate() {
            smt.comment(format!("{}: {}", t_fn.name, p));
            let name = format!("t_fn-{}", i);
            smt.assert(Term::named(expr::expr_to_smt2(p, "st"), name));
        }

        for (i, p) in m_fn.requires.iter().enumerate() {
            smt.comment(format!("{}: {}", f_fn.name, p));
            let name = format!("m_fn-{}", i);
            smt.assert(Term::named(expr::expr_to_smt2(p, "st"), name));
        }

        // smt.echo(String::from("preconditions"));
        smt.check_sat();
        smt.get_unsat_core();

        let mut smtctx = Smt2Context::new();
        smtctx.level(smt);

        let q = Z3Query::from(smtctx);
        let ticket = self
            .workerpool
            .submit_query(q)
            .expect("failed to submit query");
        let result = self.workerpool.wait_for_result(ticket);

        let mut res = result.result().lines();
        if Some("sat") == res.next() {
        } else {
            let conflicts = res.next().unwrap();
            let mut toks = conflicts[1..conflicts.len() - 1]
                .split(" ")
                .collect::<Vec<&str>>();

            let toks = toks
                .iter_mut()
                .map(|t| {
                    if t.starts_with("f_fn") {
                        let i = t[5..].parse::<usize>().unwrap();
                        &f_fn.requires[i]
                    } else if t.starts_with("t_fn") {
                        let i = t[5..].parse::<usize>().unwrap();
                        &t_fn.requires[i]
                    } else if t.starts_with("m_fn") {
                        let i = t[5..].parse::<usize>().unwrap();
                        &m_fn.requires[i]
                    } else {
                        unreachable!()
                    }
                })
                .collect::<Vec<&Expr>>();

            VrsError::new_unsat(
                String::from("Unable to satisfy the function pre-conditions."),
                toks[0].loc(),
                toks[1].loc(),
            )
            .print();
        }

        // TODO: return error if there was unsat
    }

    fn check_programs(
        &mut self,
        m_fn: &Method,
        g_fn: &Method,
        idx: Option<usize>,
        mut progs: Vec<Program>,
    ) -> Vec<Z3Ticket> {
        let mut tickets = Vec::new();
        for (i, prog) in progs.drain(..).enumerate() {
            let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

            let mut vars = vec![SortedVar::new(
                String::from("st!0"),
                String::from("Model_t"),
            )];

            for a in &m_fn.args {
                vars.push(SortedVar::new(
                    a.name.clone(),
                    types::type_to_smt2(&a.ptype),
                ));
            }

            let mut assm_args = vec![Term::ident(String::from("st!0"))];
            for a in g_fn.args.iter() {
                assm_args.push(Term::ident(a.name.clone()));
            }

            let pre = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

            let mut fn_args = vec![Term::ident(String::from("st!0"))];
            for v in m_fn.args.iter() {
                fn_args.push(Term::ident(v.name.clone()));
            }

            let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
            for a in g_fn.args.iter() {
                check_args.push(Term::ident(a.name.clone()));
            }

            let check = if let Some(i) = idx {
                Term::fn_apply(format!("{}.pre.{}", g_fn.name, i), check_args)
            } else {
                Term::fn_apply(format!("{}.pre", g_fn.name), check_args)
            };

            let t = Term::forall(vars, pre.implies(check));

            smt.assert(t);
            smt.check_sat();

            symvars.add_get_values(&mut smt);

            let mut smtctx = Smt2Context::new();
            smtctx.subsection(String::from("Verification"));
            smtctx.level(smt);

            let mut query = Z3Query::from(smtctx);
            query.set_program(prog);

            let ticket = self
                .workerpool
                .submit_query(query)
                .expect("failed to submit query");

            tickets.push(ticket);
        }
        tickets
    }

    fn obtain_sat_results(&mut self, mut fn_tickets: Vec<Vec<Z3Ticket>>) -> Vec<Vec<Z3Result>> {
        let mut fn_results = Vec::new();
        for tickets in fn_tickets.drain(..) {
            let mut results = Vec::new();
            for t in tickets {
                let res = self.workerpool.wait_for_result(t);
                let mut reslines = res.result().lines();
                if Some("sat") == reslines.next() {
                    results.push(res);
                }
            }
            if results.is_empty() {
                println!("no sat program");
            }
            fn_results.push(results);
        }
        fn_results
    }

    fn add_synth_map_tasks(&mut self, unit: &mut Segment) {
        // get the map functions
        let m_fn = unit.get_method("map").unwrap();
        // get the translate function
        let t_fn = unit.get_method("translate").unwrap();
        // get the translate function
        let f_fn = unit.get_method("matchflags").unwrap();

        // --------------------------------------------------------------------------------------
        // Check whether the pre-conditions can be satisfied
        // --------------------------------------------------------------------------------------

        self.check_precondition_satisfiability(m_fn, t_fn, f_fn);

        // --------------------------------------------------------------------------------------
        // Translate: Add a query for each of the pre-conditions of the function
        // --------------------------------------------------------------------------------------

        let mut t_fn_tickets = Vec::new();

        for (i, pre) in t_fn
            .requires
            .iter()
            .filter(|p| p.has_state_references())
            .enumerate()
        {
            let state_syms = pre.get_state_references();

            let state_bits = unit.state.referenced_field_bits(&state_syms);
            let mut st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split(".");
                let _ = parts.next();
                let field = parts.next().unwrap();
                let slice = parts.next().unwrap();

                builder.add_field_slice(field, slice);
            }

            let mut progs = builder.construct_programs(false);

            let tickets = self.check_programs(m_fn, t_fn, Some(i), progs);
            t_fn_tickets.push(tickets);

            let mut progs = builder.construct_programs(true);

            // TODO: construct the task
        }

        // --------------------------------------------------------------------------------------
        // Matchflags: Add a query for each of the pre-conditions of the function
        // --------------------------------------------------------------------------------------

        let mut f_fn_tickets = Vec::new();
        for (i, pre) in f_fn
            .requires
            .iter()
            .filter(|p| p.has_state_references())
            .enumerate()
        {
            let state_syms = pre.get_state_references();

            let state_bits = unit.state.referenced_field_bits(&state_syms);
            let mut st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split(".");
                let _ = parts.next();
                let field = parts.next().unwrap();
                let slice = parts.next().unwrap();

                builder.add_field_slice(field, slice);
            }

            let mut progs = builder.construct_programs(false);

            let tickets = self.check_programs(m_fn, f_fn, Some(i), progs);
            f_fn_tickets.push(tickets);

            let mut progs = builder.construct_programs(true);

            // TODO: construct the task
        }

        // --------------------------------------------------------------------------------------
        // Translate: check translation result
        // --------------------------------------------------------------------------------------

        // --------------------------------------------------------------------------------------
        // Collect and combine the results of the queries, verify again
        // --------------------------------------------------------------------------------------

        let mut t_fn_results = self.obtain_sat_results(t_fn_tickets);
        let mut f_fn_results = self.obtain_sat_results(f_fn_tickets);

        let mut prog_fragments = Vec::new();
        for p in t_fn_results.iter() {
            if p.is_empty() {
                println!("ERROR: no solution found for translate");
                continue;
            }
            prog_fragments.push(p[0].query().program().unwrap());
        }

        for p in f_fn_results.iter() {
            if p.is_empty() {
                println!("ERROR: no solution found for translate");
                continue;
            }
            prog_fragments.push(p[0].query().program().unwrap());
        }

        // merge the programs
        let prog = prog_fragments
            .iter_mut()
            .fold(Program::new(), |mut acc, x| acc.merge(x));

        let mut tickets = self.check_programs(m_fn, f_fn, None, vec![prog.clone()]);
        tickets.extend(self.check_programs(m_fn, t_fn, None, vec![prog.clone()]));

        for t in tickets {
            let res = self.workerpool.wait_for_result(t);
            let mut reslines = res.result().lines();
            match reslines.next() {
                Some("sat") => (),
                _ => {
                    println!("ERROR: combined solution doesn't hold!");
                }
            }
        }

        println!("found candidate program: {:?}", prog);

        unit.map_ops = Some(prog.into());
    }

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
    }

    fn add_synth_unmap_tasks(&mut self, unit: &Segment) {
        // get the unmap functions
        let m_fn = unit.get_method("unmap").unwrap();
        // get the translate function
        let t_fn = unit.get_method("translate").unwrap();
    }

    /// synthesizes the 'unmap' function and returns an ast of it
    pub fn synth_unmap(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
        for unit in &mut ast.segment_units_mut() {
            println!(
                "synthesizing unmap: for {} in {:?}",
                unit.name(),
                self.outdir
            );

            // // create the base unit context that provides the framework for synthesis
            // let ctx = self.create_unit_context(unit);

            // // perform worker reset and init with the given context
            // self.workerpool.reset_with_context(Z3Query::from(ctx));

            // self.add_synth_unmap_tasks(unit);

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

            // // create the base unit context that provides the framework for synthesis
            // let ctx = self.create_unit_context(unit);

            // // perform worker reset and init with the given context
            // self.workerpool.reset_with_context(Z3Query::from(ctx));

            // self.add_synth_protect_tasks(unit);

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
