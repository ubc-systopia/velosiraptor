// VelosiParser -- a parser for the Velosiraptor Language
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

//! # VelosiParser -- The Velosiraptor Parser
//!
//! The VelosiParser consumes the lexed TokenStream and produces a parse tree for the
//! for further processing.

// used standard library functionality

use std::env;
use std::path::PathBuf;
use std::rc::Rc;

use smt2::Smt2Context;

// public re-exports

// crate modules
mod error;
mod model;
mod operation;
mod programs;
mod vmops;
mod z3;

use velosiast::ast::VelosiAstUnitSegment;

pub use error::{VelosiSynthError, VelosiSynthIssues};
pub use operation::{OpExpr, Operation};
pub use programs::{Program, ProgramsBuilder};
pub use z3::{Z3Query, Z3Ticket, Z3WorkerPool};

#[macro_export]
macro_rules! synth_result_return (($res: expr, $issues: expr) => (
    if $issues.is_ok() {
        Result::Ok($res)
    } else {
        Result::Err($issues)
    }
));

#[macro_export]
macro_rules! synth_result_unwrap (($e: expr, $issues: expr) => (
    match $e {
        Result::Ok(t) => t,
        Result::Err(e) => {
            $issues.merge(e.into());
            return Result::Err($issues)
        },
    }
));

pub struct SynthZ3 {
    ast: Rc<VelosiAstUnitSegment>,
    outdir: PathBuf,
    ncpu: usize,
    workerpool: Option<Z3WorkerPool>,
}

impl SynthZ3 {
    pub fn new(ast: Rc<VelosiAstUnitSegment>) -> Self {
        // get the outdir from the current path
        let outdir = env::current_dir().unwrap();
        let outdir = outdir.join("synth");

        Self::with_outdir(ast, outdir)
    }

    pub fn with_outdir(ast: Rc<VelosiAstUnitSegment>, outdir: PathBuf) -> Self {
        Self::with_ncpu(ast, outdir, 1)
    }

    pub fn with_ncpu(ast: Rc<VelosiAstUnitSegment>, outdir: PathBuf, ncpu: usize) -> Self {
        SynthZ3 {
            ast,
            outdir,
            ncpu,
            workerpool: None,
        }
    }

    pub fn set_parallelism(&mut self, ncpu: usize) {
        // make sure we don't have anything running anymore
        self.terminate();

        let workerpool = Z3WorkerPool::with_num_workers(ncpu, Some(&self.outdir));

        self.workerpool = Some(workerpool);
        self.ncpu = ncpu;
    }

    pub fn terminate(&mut self) {
        if let Some(mut workerpool) = self.workerpool.take() {
            workerpool.terminate();
        }
    }

    fn run_smt2(&mut self, ctx: Smt2Context) -> Result<(), VelosiSynthIssues> {
        if self.workerpool.is_none() {
            let workerpool = Z3WorkerPool::with_num_workers(self.ncpu, Some(&self.outdir));
            self.workerpool = Some(workerpool);
        }

        let workerpool = self.workerpool.as_mut().unwrap();
        workerpool.reset_with_context(Z3Query::from(ctx));
        Ok(())
    }

    pub fn create_model(&mut self) -> Result<(), VelosiSynthIssues> {
        self.run_smt2(model::create(&self.ast))?;
        Ok(())
    }

    pub fn sanity_check(&mut self) -> Result<(), VelosiSynthIssues> {
        let mut issues = VelosiSynthIssues::new();

        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "map",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "unmap",
        ));
        issues.merge_result(vmops::sanity::check_precondition_satisfiability(
            &mut self.workerpool.as_mut().unwrap(),
            &self.ast,
            "protect",
        ));

        synth_result_return!((), issues)
    }

    // fn add_check_for_precondition(
    //     &mut self,
    //     m_fn: &Method,
    //     progs: &mut Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2("map", m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];
    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let pre = Term::fn_apply(
    //             String::from("translate.assms"),
    //             vec![
    //                 Term::ident(String::from("st!0")),
    //                 Term::ident(String::from("va")),
    //             ],
    //         );

    //         let mut map_fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             map_fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let check = Term::fn_apply(
    //             String::from("translate.pre"),
    //             vec![
    //                 Term::fn_apply(String::from("map"), map_fn_args),
    //                 Term::ident(String::from("va")),
    //             ],
    //         );

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         match self.workerpool.submit_query(query) {
    //             Ok(t) => {
    //                 println!("Submitted query: {}", t);
    //             }
    //             Err(_e) => {
    //                 println!("Failed to submit query.");
    //             }
    //         }
    //     }
    //     Vec::new()
    // }

    // fn check_programs_translate(
    //     &mut self,
    //     m_fn: &Method,
    //     g_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in g_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in m_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
    //         for a in m_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let check = Term::fn_apply(format!("{}.result.{}", g_fn.name, m_fn.name), check_args);

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn check_programs_matchflags(
    //     &mut self,
    //     m_fn: &Method,
    //     g_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &m_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in g_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", g_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in m_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", m_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in m_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(m_fn.name.clone(), fn_args)];
    //         for a in g_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let check = Term::fn_apply(g_fn.name.to_string(), check_args);

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn check_programs_protect(
    //     &mut self,
    //     p_fn: &Method,
    //     f_fn: &Method,
    //     t_fn: &Method,
    //     mut progs: Vec<Program>,
    // ) -> Vec<Z3Ticket> {
    //     let mut tickets = Vec::new();
    //     for (_i, prog) in progs.drain(..).enumerate() {
    //         let (mut smt, symvars) = prog.to_smt2(&p_fn.name, p_fn.args.as_slice());

    //         let mut vars = vec![SortedVar::new(
    //             String::from("st!0"),
    //             String::from("Model_t"),
    //         )];

    //         for a in &p_fn.args {
    //             vars.push(SortedVar::new(
    //                 a.name.clone(),
    //                 types::type_to_smt2(&a.ptype),
    //             ));
    //         }

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in f_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }

    //         let pre1 = Term::fn_apply(format!("{}.assms", t_fn.name), assm_args);

    //         let mut assm_args = vec![Term::ident(String::from("st!0"))];
    //         for a in f_fn.args.iter() {
    //             assm_args.push(Term::ident(a.name.clone()));
    //         }
    //         let pre2 = Term::fn_apply(format!("{}.assms", f_fn.name), assm_args);

    //         let pre = Term::land(pre1, pre2);

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];
    //         for v in p_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }

    //         let mut check_args = vec![Term::fn_apply(p_fn.name.clone(), fn_args)];
    //         for a in f_fn.args.iter() {
    //             check_args.push(Term::ident(a.name.clone()));
    //         }

    //         let mut fn_args = vec![Term::ident(String::from("st!0"))];

    //         //  ((st!0 Model_t) (st!1 Model_t) (va VAddr_t) (sz Size_t)) Bool
    //         for v in p_fn.args.iter() {
    //             fn_args.push(Term::ident(v.name.clone()));
    //         }
    //         let mut t_fn_check_args = vec![
    //             Term::ident(String::from("st!0")),
    //             Term::fn_apply(p_fn.name.clone(), fn_args),
    //         ];
    //         t_fn_check_args.push(Term::ident("va".to_string()));
    //         t_fn_check_args.push(Term::ident("sz".to_string()));

    //         // for a in t_fn.args.iter() {
    //         //     t_fn_check_args.push(Term::ident(a.name.clone()));
    //         // }

    //         let check = Term::land(
    //             Term::fn_apply(f_fn.name.to_string(), check_args),
    //             Term::fn_apply(format!("{}.result.protect", t_fn.name), t_fn_check_args),
    //         );

    //         let t = Term::forall(vars, pre.implies(check));

    //         smt.assert(t);
    //         smt.check_sat();

    //         symvars.add_get_values(&mut smt);

    //         let mut smtctx = Smt2Context::new();
    //         smtctx.subsection(String::from("Verification"));
    //         smtctx.level(smt);

    //         let mut query = Z3Query::from(smtctx);
    //         query.set_program(prog);

    //         let ticket = self
    //             .workerpool
    //             .submit_query(query)
    //             .expect("failed to submit query");

    //         tickets.push(ticket);
    //     }
    //     tickets
    // }

    // fn obtain_sat_results(&mut self, mut fn_tickets: Vec<Vec<Z3Ticket>>) -> Vec<Vec<Z3Result>> {
    //     let mut fn_results = Vec::new();
    //     for tickets in fn_tickets.drain(..) {
    //         let mut results = Vec::new();
    //         for t in tickets {
    //             let mut res = self.workerpool.wait_for_result(t);

    //             // res.print_timestamps();

    //             let output = res.result();

    //             let mut reslines = output.lines();
    //             if Some("sat") == reslines.next() {
    //                 if reslines.next().is_some() {
    //                     match resultparser::parse_result(&output[4..]) {
    //                         Ok(mut vars) => {
    //                             if !vars.is_empty() {
    //                                 // println!("rewriting the program: {:?}\n", vars);
    //                                 res.query_mut()
    //                                     .program_mut()
    //                                     .replace_symbolic_values(&mut vars);
    //                             }
    //                         }
    //                         Err(_e) => (),
    //                     }
    //                 }
    //                 results.push(res);
    //             }
    //         }
    //         if results.is_empty() {
    //             println!("no sat program");
    //         }
    //         fn_results.push(results);
    //     }
    //     fn_results
    // }

    // /// synthesizes the `map` function and returns an ast of it
    // pub fn synth_map(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
    //     for unit in &mut ast.segment_units_mut() {
    //         println!("synthesizing map: for {} in {:?}", unit.name(), self.outdir);
    //         // create the base unit context that provides the framework for synthesis
    //         let ctx = self.create_unit_context(unit);

    //         // perform worker reset and init with the given context
    //         self.workerpool.reset_with_context(Z3Query::from(ctx));

    //         let tickets = self.add_synth_map_tasks(unit);
    //         self.check_synth_map_tasks(unit, tickets);
    //     }

    //     Ok(())
    // }

    // /// synthesizes the 'unmap' function and returns an ast of it
    // pub fn synth_unmap(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
    //     for unit in &mut ast.segment_units_mut() {
    //         println!(
    //             "synthesizing unmap: for {} in {:?}",
    //             unit.name(),
    //             self.outdir
    //         );

    //         // create the base unit context that provides the framework for synthesis
    //         let ctx = self.create_unit_context(unit);

    //         // perform worker reset and init with the given context
    //         self.workerpool.reset_with_context(Z3Query::from(ctx));

    //         let tickets = self.add_synth_unmap_tasks(unit);
    //         self.check_synth_unmap_tasks(unit, tickets);
    //     }

    //     Ok(())
    // }

    // pub fn synth_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
    //     for unit in &mut ast.segment_units_mut() {
    //         println!(
    //             "synthesizing protect: for {} in {:?}",
    //             unit.name(),
    //             self.outdir
    //         );

    //         // create the base unit context that provides the framework for synthesis
    //         let ctx = self.create_unit_context(unit);

    //         // perform worker reset and init with the given context
    //         self.workerpool.reset_with_context(Z3Query::from(ctx));

    //         let tickets = self.add_synth_protect_tasks(unit);
    //         self.check_synth_protect_tasks(unit, tickets);
    //     }

    //     Ok(())
    // }

    // pub fn synth_map_unmap_protect(&mut self, ast: &mut AstRoot) -> Result<(), SynthError> {
    //     for unit in &mut ast.segment_units_mut() {
    //         let ctx = self.create_unit_context(unit);
    //         self.workerpool.reset_with_context(Z3Query::from(ctx));

    //         let m_tickets = self.add_synth_map_tasks(unit);
    //         let u_tickets = self.add_synth_unmap_tasks(unit);
    //         let p_tickets = self.add_synth_protect_tasks(unit);

    //         self.check_synth_map_tasks(unit, m_tickets);
    //         self.check_synth_unmap_tasks(unit, u_tickets);
    //         self.check_synth_protect_tasks(unit, p_tickets);
    //     }
    //     Ok(())
    // }
}
