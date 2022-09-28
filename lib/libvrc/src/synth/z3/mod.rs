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

use custom_error::custom_error;

use smt2::{Smt2Context, Smt2Option, SortedVar, Term, VarDecl};

use crate::ast::{AstNodeGeneric, AstRoot, Expr, Method, Segment};
use crate::error::VrsError;
use crate::synth::SynthError;

use self::operations::Program;
use self::query::{Z3Query, Z3Result, Z3Ticket};
use self::worker::Z3WorkerPool;

pub mod consts;
pub mod expr;
pub mod field;
pub mod instance;
pub mod interface;
pub mod method;
pub mod model;
pub mod operations;
pub mod query;
pub mod resultparser;
pub mod state;
pub mod types;
pub mod worker;

custom_error! {#[derive(PartialEq, Eq)] pub Z3Error
    ResulteParseError  = "Failed to aprse the result",
    QueryError = "Failed to execute the query",
    GenericError = "Generic Z3 Error",
}

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
        model::add_model_def(&mut smt, unit);
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

    fn add_check_for_precondition(
        &mut self,
        m_fn: &Method,
        progs: &mut Vec<Program>,
    ) -> Vec<Z3Ticket> {
        for (_i, prog) in progs.drain(..).enumerate() {
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
                Err(_e) => {
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
                .split(' ')
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

    fn check_programs_translate(
        &mut self,
        m_fn: &Method,
        g_fn: &Method,
        mut progs: Vec<Program>,
    ) -> Vec<Z3Ticket> {
        let mut tickets = Vec::new();
        for (_i, prog) in progs.drain(..).enumerate() {
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

            let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

            let mut assm_args = vec![Term::ident(String::from("st!0"))];
            for a in m_fn.args.iter() {
                assm_args.push(Term::ident(a.name.clone()));
            }
            let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

            let pre = Term::land(pre1, pre2);

            let mut fn_args = vec![Term::ident(String::from("st!0"))];
            for v in m_fn.args.iter() {
                fn_args.push(Term::ident(v.name.clone()));
            }

            let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
            for a in m_fn.args.iter() {
                check_args.push(Term::ident(a.name.clone()));
            }

            let check = Term::fn_apply(format!("{}.result.{}", g_fn.name, m_fn.name), check_args);

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

    fn check_programs_precond(
        &mut self,
        m_fn: &Method,
        g_fn: &Method,
        idx: Option<usize>,
        negate: bool,
        mut progs: Vec<Program>,
    ) -> Vec<Z3Ticket> {
        let mut tickets = Vec::new();
        for (_i, prog) in progs.drain(..).enumerate() {
            let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

            let vars = vec![
                SortedVar::new(String::from("st!0"), String::from("Model_t")),
                SortedVar::new(String::from("va"), String::from("VAddr_t")),
                SortedVar::new(String::from("sz"), String::from("Size_t")),
                SortedVar::new(String::from("pa"), String::from("PAddr_t")),
                SortedVar::new(String::from("flgs"), String::from("Flags_t")),
            ];

            // for a in &m_fn.args {
            //     vars.push(SortedVar::new(
            //         a.name.clone(),
            //         types::type_to_smt2(&a.ptype),
            //     ));
            // }

            let mut assm_args = vec![Term::ident(String::from("st!0"))];
            for a in g_fn.args.iter() {
                assm_args.push(Term::ident(a.name.clone()));
            }

            let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

            let mut assm_args = vec![Term::ident(String::from("st!0"))];
            for a in m_fn.args.iter() {
                assm_args.push(Term::ident(a.name.clone()));
            }
            let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

            let pre = Term::land(pre1, pre2);

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

            let t = if negate {
                Term::forall(vars, pre.implies(Term::lnot(check)))
            } else {
                Term::forall(vars, pre.implies(check))
            };

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
                let mut res = self.workerpool.wait_for_result(t);
                let mut reslines = res.result().lines();
                if Some("sat") == reslines.next() {
                    if let Some(s) = reslines.next() {
                        let mut vars = resultparser::parse_result(s).expect(
                            "
                        failed to parse the result",
                        );

                        if !vars.is_empty() {
                            println!("rewriting the program: {:?}\n", vars);
                            res.query_mut()
                                .program_mut()
                                .replace_symbolic_values(&mut vars);
                        }
                    }
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
            let st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split('.');
                let _ = parts.next();
                let field = parts.next().unwrap();
                if let Some(slice) = parts.next() {
                    builder.add_field_slice(field, slice);
                } else {
                    //builder.add_field(field);
                }
            }

            let progs = builder.construct_programs(false);

            let tickets = self.check_programs_precond(m_fn, t_fn, Some(i), false, progs);
            t_fn_tickets.push(tickets);

            // let _progs = builder.construct_programs(true);

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
            let st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split('.');
                let _ = parts.next();
                let field = parts.next().unwrap();
                let slice = parts.next().unwrap();

                builder.add_field_slice(field, slice);
            }

            let progs = builder.construct_programs(false);

            let tickets = self.check_programs_precond(m_fn, f_fn, Some(i), false, progs);
            f_fn_tickets.push(tickets);

            // let progs = builder.construct_programs(true);

            // TODO: construct the task
        }

        // --------------------------------------------------------------------------------------
        // Translate: check translation result
        // --------------------------------------------------------------------------------------

        let tr_res_tickets = {
            let state_syms = t_fn.get_state_references_body();
            let state_bits = unit.state.referenced_field_bits(&state_syms);
            let st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split('.');
                let _ = parts.next();
                let field = parts.next().unwrap();
                let slice = parts.next().unwrap();

                builder.add_field_slice(field, slice);
            }

            let progs = builder.construct_programs(true);
            self.check_programs_translate(m_fn, t_fn, progs)
        };

        // --------------------------------------------------------------------------------------
        // Matchflags: check the expression result
        // --------------------------------------------------------------------------------------

        // todo

        // --------------------------------------------------------------------------------------
        // Collect and combine the results of the queries, verify again
        // --------------------------------------------------------------------------------------

        let results = {
            let mut results = Vec::new();

            let t_fn_results = self.obtain_sat_results(t_fn_tickets);
            let f_fn_results = self.obtain_sat_results(f_fn_tickets);
            let tr_results = self.obtain_sat_results(vec![tr_res_tickets]);

            results.extend(t_fn_results);
            results.extend(f_fn_results);
            results.extend(tr_results);
            results
        };

        // the completed candidate program
        let mut candidate_programs: Vec<Vec<&Program>> = vec![Vec::new()];

        for res in results.iter() {
            // new candidate programs
            let mut new_candidate_programs = Vec::new();

            for prog in candidate_programs {
                for r in res {
                    // expand all candidate programs with the new program
                    let mut new_prog = prog.clone();
                    new_prog.push(r.query().program().unwrap());
                    new_candidate_programs.push(new_prog);
                }
            }

            // update the candidate programs
            candidate_programs = new_candidate_programs;
        }

        let mut candidate_programs: Vec<Program> = candidate_programs
            .iter_mut()
            .map(|p| p.iter_mut().fold(Program::new(), |acc, x| acc.merge(x)))
            .collect();

        for prog in candidate_programs.drain(..) {
            let mut p_tickets =
                self.check_programs_precond(m_fn, f_fn, None, false, vec![prog.clone()]);
            p_tickets.extend(self.check_programs_precond(
                m_fn,
                t_fn,
                None,
                false,
                vec![prog.clone()],
            ));
            p_tickets.extend(self.check_programs_translate(m_fn, t_fn, vec![prog.clone()]));

            let mut all_sat = true;
            for t in p_tickets {
                let res = self.workerpool.wait_for_result(t);
                let mut reslines = res.result().lines();
                all_sat &= reslines.next() == Some("sat");
            }
            if all_sat {
                println!("found candidate program: {:?}", prog);
                unit.map_ops = Some(prog.into());
                return;
            }
        }
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

        Ok(())
    }

    fn add_synth_unmap_tasks(&mut self, unit: &mut Segment) {
        // get the map functions
        let m_fn = unit.get_method("unmap").unwrap();
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
            let st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split('.');
                let _ = parts.next();
                let field = parts.next().unwrap();
                if let Some(slice) = parts.next() {
                    builder.add_field_slice(field, slice);
                } else {
                    //builder.add_field(field);
                }
            }

            let progs = builder.construct_programs(false);

            let tickets = self.check_programs_precond(m_fn, t_fn, Some(i), true, progs);
            t_fn_tickets.push(tickets);

            // let progs = builder.construct_programs(true);

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
            let st_access_fields = unit
                .interface
                .fields_accessing_state(&state_syms, &state_bits);

            // construct the program builder
            let mut builder = operations::ProgramsBuilder::new();
            for v in m_fn.args.iter() {
                builder.add_var(v.name.clone());
            }

            for f in st_access_fields.iter() {
                let mut parts = f.split('.');
                let _ = parts.next();
                let field = parts.next().unwrap();
                let slice = parts.next().unwrap();

                builder.add_field_slice(field, slice);
            }

            let progs = builder.construct_programs(false);

            let tickets = self.check_programs_precond(m_fn, f_fn, Some(i), true, progs);
            f_fn_tickets.push(tickets);

            // let progs = builder.construct_programs(true);

            // TODO: construct the task
        }

        let results = {
            let mut results = Vec::new();

            let t_fn_results = self.obtain_sat_results(t_fn_tickets);
            let f_fn_results = self.obtain_sat_results(f_fn_tickets);

            results.extend(t_fn_results);
            results.extend(f_fn_results);
            results
        };

        // the completed candidate program
        let mut candidate_programs: Vec<Vec<&Program>> = vec![Vec::new()];

        for res in results.iter() {
            // new candidate programs
            let mut new_candidate_programs = Vec::new();

            for prog in candidate_programs {
                for r in res {
                    // expand all candidate programs with the new program
                    let mut new_prog = prog.clone();
                    new_prog.push(r.query().program().unwrap());
                    new_candidate_programs.push(new_prog);
                }
            }

            // update the candidate programs
            candidate_programs = new_candidate_programs;
        }

        let mut candidate_programs: Vec<Program> = candidate_programs
            .iter_mut()
            .map(|p| p.iter_mut().fold(Program::new(), |acc, x| acc.merge(x)))
            .collect();

        for prog in candidate_programs.drain(..) {
            let mut p_tickets =
                self.check_programs_precond(m_fn, f_fn, None, true, vec![prog.clone()]);
            p_tickets.extend(self.check_programs_precond(
                m_fn,
                t_fn,
                None,
                true,
                vec![prog.clone()],
            ));

            let mut all_sat = true;
            for t in p_tickets {
                let res = self.workerpool.wait_for_result(t);
                let mut reslines = res.result().lines();
                all_sat &= reslines.next() == Some("sat");
            }
            if all_sat {
                println!("found candidate program: {:?}", prog);
                unit.unmap_ops = Some(prog.into());
                return;
            }
        }
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
