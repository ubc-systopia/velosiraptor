// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Synthesis of Virtual Memory Operations

pub mod sanity;

// fn check_programs_precond(
//     &mut self,
//     m_fn: &Method,
//     g_fn: &Method,
//     idx: Option<usize>,
//     negate: bool,
//     mut progs: Vec<Program>,
// ) -> Vec<Z3Ticket> {

//     let mut tickets = Vec::new();
//     for (_i, prog) in progs.drain(..).enumerate() {
//         let (mut smt, symvars) = prog.to_smt2(&m_fn.name, m_fn.args.as_slice());

//         let vars = vec![
//             SortedVar::new(String::from("st!0"), model::types::model()),
//             SortedVar::new(String::from("va"), String::from("VAddr_t")),
//             SortedVar::new(String::from("sz"), String::from("Size_t")),
//             SortedVar::new(String::from("pa"), String::from("PAddr_t")),
//             SortedVar::new(String::from("flgs"), String::from("Flags_t")),
//         ];

//         // for a in &m_fn.args {
//         //     vars.push(SortedVar::new(
//         //         a.name.clone(),
//         //         types::type_to_smt2(&a.ptype),
//         //     ));
//         // }

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

//         let check = if let Some(i) = idx {
//             Term::fn_apply(format!("{}.pre.{}", g_fn.name, i), check_args)
//         } else {
//             Term::fn_apply(format!("{}.pre", g_fn.name), check_args)
//         };

//         let t = if negate {
//             Term::forall(vars, pre.implies(Term::lnot(check)))
//         } else {
//             Term::forall(vars, pre.implies(check))
//         };

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
