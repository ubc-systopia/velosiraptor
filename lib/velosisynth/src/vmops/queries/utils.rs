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

//! Synthesis of Virtual Memory Operations: Map

use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use velosiast::{
    ast::{
        VelosiAstBinOp, VelosiAstExpr, VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr,
        VelosiAstIdentifier, VelosiAstMethod, VelosiAstMethodProperty, VelosiAstTypeInfo,
        VelosiAstUnitSegment,
    },
    VelosiAstInterfaceField,
};

use crate::opts::SynthOpts;
use crate::{
    model::{
        method::{translate_range_name, translate_range_name_protect},
        types,
        velosimodel::{model_get_fn_name, WBUFFER_PREFIX},
    },
    Program, ProgramsBuilder, ProgramsIter,
};
use smt2::Term;

use super::resultparser;
use super::{BoolExprQueryBuilder, CompoundBoolExprQueryBuilder, ProgramBuilder, ProgramVerifier};

use crate::z3::Z3TaskPriority;

pub fn make_program_builder_no_params(
    unit: &VelosiAstUnitSegment,
    expr: &VelosiAstExpr,
    additional_state: HashSet<Rc<String>>,
    lower_bound: bool,
    opts: &SynthOpts,
) -> ProgramsBuilder {
    log::info!(target: "[vmops::utils]", "constructing programs for {expr}");
    // obtain the state references in the pre-condition
    let mut state_syms = additional_state;

    // if the state optimization is disabled, then we take the entire state as being relevant for
    // this expression, other wise we only take the parts of the state that actually appears in the
    // expression.
    if opts.disable_state_opt {
        state_syms.extend(unit.state_bit_slice_idents());
    } else {
        expr.get_state_references(&mut state_syms);
    }

    // obtain the bits of the state that are relevant based on the state references
    let state_bits = unit.state.get_field_slice_refs(&state_syms);

    // if the interface optimization is disabled we simply take the entire interface as being
    // relevant otherwise, we perform a back projection to obtain the relevant interface fields.
    let st_access_fields = if opts.disable_iface_opt {
        unit.interface.bit_slice_idents()
    } else {
        unit.interface
            .fields_accessing_state(&state_syms, &state_bits)
    };

    // construct the program builder
    let mut builder = ProgramsBuilder::new();

    // add the fields to the program builder
    for f in st_access_fields.iter() {
        let mut parts = f.split('.');
        let _ = parts.next();
        let fieldname = parts.next().unwrap();

        let field = unit
            .interface
            .field(fieldname)
            .expect("didn't find the field");

        if let VelosiAstInterfaceField::Instruction(_f) = field {
            builder.add_instruction(fieldname.to_string());
        } else if let Some(slicename) = parts.next() {
            let slice = field.slice(slicename).expect("didn't find the slice");
            builder.add_field_slice(fieldname, slicename, slice.start, slice.nbits() as usize);
        } else {
            builder.add_field(fieldname.to_string());
        }
    }

    // println!("EXPR: {expr}");
    if expr.has_translate_range() && !lower_bound && !state_syms.is_empty() {
        builder.set_limit();
        if state_syms.len() > 1 {
            builder.set_limit_expression();
        }
    }

    builder
}

pub fn make_program_builder(
    unit: &VelosiAstUnitSegment,
    m_goal: &VelosiAstMethod,
    expr: &VelosiAstExpr,
    additional_state: HashSet<Rc<String>>,
    lower_bound: bool,
    opts: &SynthOpts,
) -> ProgramsBuilder {
    let mut builder =
        make_program_builder_no_params(unit, expr, additional_state, lower_bound, opts);

    let mut vars = HashSet::new();
    for id in expr.get_var_references().iter() {
        let mut parts = id.ident().as_str().split('.');
        if let Some(part) = parts.next() {
            vars.insert(part);
        }
        vars.insert(id.ident().as_str());
    }

    // add the variables that the function talks about
    for v in m_goal.params.iter() {
        // flags show up differently
        if v.ptype.is_flags() {
            if let Some(flags) = &unit.flags {
                let var = Arc::new(v.ident_to_string());

                let mut buf = String::with_capacity(30);
                for f in flags.flags.iter() {
                    buf.push_str(var.as_str());
                    buf.push('.');
                    buf.push_str(f.as_str());

                    if vars.contains(buf.as_str()) {
                        builder.add_flags(var.clone(), f.to_string());
                    }

                    buf.clear();
                }
            } else {
                unreachable!("should have defined flags!");
            }
        } else {
            builder.add_var(v.ident_to_string());
        }
    }

    builder
}

pub fn make_program_iter_mem(prog: &Program) -> ProgramsIter {
    let programs = prog.generate_possible_barriers();
    let stat_max_programs = programs.len() as u128;

    ProgramsIter {
        programs,
        stat_num_programs: 0,
        stat_max_programs,
    }
}

#[derive(PartialEq, Eq)]
pub enum QueryResult {
    Sat,
    Unsat,
    Unknown,
    Error,
}

pub fn check_result(output: &str, program: &mut Program) -> QueryResult {
    let mut reslines = output.lines();
    match reslines.next() {
        Some("sat") => {
            log::debug!(target: "[CheckResult]", " - sat: {:?}", program);
            if reslines.next().is_some() {
                match resultparser::parse_result(&output[4..]) {
                    Ok(mut vars) => {
                        if !vars.is_empty() {
                            program.replace_symbolic_values(&mut vars);
                        }
                    }
                    Err(_e) => (),
                }
            }
            QueryResult::Sat
        }
        Some("unsat") => {
            log::trace!(target: "[CheckResult]", " - unsat: {:?}", program);
            QueryResult::Unsat
        }
        Some("unknown") => {
            log::trace!(target: "[CheckResult]", " - unknown: {:?}", program);
            QueryResult::Unknown
        }
        Some(a) => {
            log::error!(target: "[CheckResult]", " - {} {:?}", a, program);
            if a.starts_with("(error") {
                QueryResult::Error
            } else {
                unreachable!("unexpected none output: {}", a);
            }
        }
        None => {
            unreachable!("unexpected none output")
        }
    }
}

pub fn add_empty_wbuffer_precond(prefix: &str, pre: Term) -> Term {
    Term::land(
        Term::eq(
            smt2::seq::empty(types::wbuffer(prefix)),
            Term::fn_apply(
                model_get_fn_name(prefix, WBUFFER_PREFIX),
                vec![Term::ident("st!0".to_string())],
            ),
        ),
        pre,
    )
}

/// this functions collects the methods tagged with `remap` and adds them to the partial programs
///
/// # Params
///
///  - `unit`:              the unit to search for methods
///  - `m_op`:              the current operation (map/protect/unmap)
///  - `batch_size`:        number of queries to emit to the verifier
///  - `negate`:            whether to negate the expression
///  - `partial_programs`:  the list of partial programs to add the queries to
pub fn add_methods_tagged_with_remap(
    unit: &VelosiAstUnitSegment,
    m_op: &Rc<VelosiAstMethod>,
    opts: &SynthOpts,
    negate: bool,
    var_refs: Option<bool>,
    partial_programs: &mut Vec<Box<dyn ProgramBuilder>>,
) {
    for r_fn in unit.methods.values() {
        // if the property is not set to remap, we don't care about it
        if !r_fn.properties.contains(&VelosiAstMethodProperty::Remap) {
            log::debug!(
                target : "[synth::utils]",
                "skipping method {} (not tagged with remap)", r_fn.ident()
            );
            continue;
        }

        // we don't care about abstract or synth methods, the return type should always be boolean
        if r_fn.is_abstract || r_fn.is_synth || !r_fn.rtype.is_boolean() {
            log::debug!(
                target : "[synth::map]",
                "skipping method {} (abstract, synth, or not boolean)", r_fn.ident()
            );
            continue;
        }

        let params = m_op.get_param_names();

        // split the body expressions into a list of conjuncts forming a CNF
        let exprs: Vec<Rc<VelosiAstExpr>> = r_fn
            .body
            .as_ref()
            .map(|body| body.split_cnf())
            .unwrap_or_else(|| panic!("no body for method {}", r_fn.ident()))
            .into_iter()
            .filter(|e| {
                if let Some(var_refs) = var_refs {
                    e.has_var_references(&params) == var_refs
                } else {
                    true
                }
            })
            .collect();

        // build the query for the expressions of the body of the function,
        let query: Option<Box<dyn ProgramBuilder>> = match exprs.as_slice() {
            [] => continue,
            [exp] => {
                log::debug!(target : "[synth::utils]", "handling {} with single expr body {}", r_fn.ident(), exp);

                // just a single expression here
                BoolExprQueryBuilder::new(unit, m_op.clone(), exp.clone())
                    // .assms(): No assumptions, as they will be added by the map.assms()
                    .negate(negate)
                    .build(opts)
                    .map(|e| e.into())
            }
            _ => {
                log::debug!(target : "[synth::utils]", "handling {} with multiple expr body (CNF)", r_fn.ident());

                // handle all the expressions
                CompoundBoolExprQueryBuilder::new(
                    unit,
                    m_op.clone(),
                    Z3TaskPriority::highest().lower().lower(),
                )
                .exprs(exprs)
                // .assms(): No assumptions, as they will be added by the map.assms()
                .negate(negate) // !(A && B && C), we convert this to !A || !B || !C
                .all(opts)
                .map(|e| e.into())
            }
        };

        // add the program verifier and add the query to the list
        if let Some(query) = query {
            log::debug!(target : "[synth::map]", "adding query to partial programs");
            partial_programs.push(
                ProgramVerifier::with_batchsize(
                    unit.ident().clone(),
                    query,
                    opts.batch_size,
                    Z3TaskPriority::lowest(),
                )
                .into(),
            );
        }
    }
}

/// this function adds the pre-conditions of the methods to the partial programs
///
/// # Params
///
///  - `unit`               the unit to search for methods
///  - `m_op`               the current operation (map/protect/unmap)
///  - `m`                  the method to take the pre-conditions from
///  - `batch_size`         the batchsize of the queries
///  - `negate`             whether to negate the expression
///  - `partial_programs`   the list of partial programs to add the queries to
pub fn add_method_preconds(
    unit: &VelosiAstUnitSegment,
    m_op: &Rc<VelosiAstMethod>,
    m: &Rc<VelosiAstMethod>,
    opts: &SynthOpts,
    negate: bool,
    var_refs: Option<bool>,
    partial_programs: &mut Vec<Box<dyn ProgramBuilder>>,
) {
    if m.ident().as_str() != "translate" {
        todo!("handling of methods other than translate is NYI");
    }

    if var_refs.is_some() {
        log::warn!("handling of var_refs is currently not fully supported yet\n");
    }

    let params = m.get_param_names();
    for (i, e) in m.requires.iter().enumerate() {
        if !e.has_state_references() {
            // if it hasn't state references then we can skip it
            continue;
        }

        if e.has_var_references(&params) && m_op.ident().as_str() == "protect" {
            // special case here as we want to make sure the results stays the same here...

            // we don't use the builder here, as we just want an "empty" program that gets
            // passed through the synthesis tree to ensure that the translation produces
            // the same output address as before changing the permission bits
            let programs = ProgramsIter::new_noop();

            let args = vec![
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        "st!0".to_string(),
                        VelosiAstTypeInfo::VirtAddr,
                    ),
                )),
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        "va".to_string(),
                        VelosiAstTypeInfo::VirtAddr,
                    ),
                )),
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        "sz".to_string(),
                        VelosiAstTypeInfo::VirtAddr,
                    ),
                )),
            ];

            // args.extend(m_op.params.iter().map(|p| Rc::new(p.as_ref().into())));

            let ident = VelosiAstIdentifier::from(translate_range_name_protect(Some(i)).as_str());

            let mut fn_call = VelosiAstFnCallExpr::new(ident, VelosiAstTypeInfo::Bool);
            fn_call.add_args(args);

            let query = BoolExprQueryBuilder::new(
                unit,
                m_op.clone(),
                Rc::new(VelosiAstExpr::FnCall(fn_call)),
            )
            // .assms(m.assms.clone())
            // .variable_references(true)
            .negate(negate) // we negate the expression here
            .programs(Box::new(programs))
            .build(opts)
            .map(|e| e.into());

            if let Some(query) = query {
                partial_programs.push(
                    ProgramVerifier::with_batchsize(
                        unit.ident().clone(),
                        query,
                        opts.batch_size,
                        Z3TaskPriority::lowest(),
                    )
                    .into(),
                );
            } else {
                panic!("no query!");
            }

            continue;
        }

        let query = if e.has_var_references(&params) {
            let binop = if let VelosiAstExpr::BinOp(pre) = e.as_ref() {
                pre
            } else {
                unreachable!();
            };

            let lower_bound = if binop.lhs.has_var_references(&params) {
                matches!(binop.op, VelosiAstBinOp::Gt | VelosiAstBinOp::Ge)
            } else {
                matches!(binop.op, VelosiAstBinOp::Lt | VelosiAstBinOp::Le)
            };

            let ident = VelosiAstIdentifier::from(translate_range_name(Some(i)).as_str());
            let args = vec![
                Rc::new(m.params[0].as_ref().into()),
                Rc::new(VelosiAstExpr::IdentLiteral(
                    VelosiAstIdentLiteralExpr::with_name(
                        String::from("sz"),
                        VelosiAstTypeInfo::Size,
                    ),
                )),
            ];

            let mut fn_call = VelosiAstFnCallExpr::new(ident, VelosiAstTypeInfo::Bool);
            fn_call.add_args(args);

            let mut staterefs = HashSet::new();
            e.get_state_references(&mut staterefs);

            BoolExprQueryBuilder::new(unit, m_op.clone(), Rc::new(VelosiAstExpr::FnCall(fn_call)))
                // .assms(m.assms.clone())
                .variable_references(!negate)
                .additional_state_refs(staterefs)
                .set_lower_bound(lower_bound)
                .negate(negate) // we negate the expression here
                .build(opts)
                .map(|e| e.into())
        } else if !negate {
            BoolExprQueryBuilder::new(unit, m_op.clone(), e.clone())
                // .assms(m.assms.clone())
                // .negate(negate) // we negate the expression here
                .build(opts)
                .map(|e| e.into())
        } else {
            None
        };

        if let Some(query) = query {
            partial_programs.push(
                ProgramVerifier::with_batchsize(
                    unit.ident().clone(),
                    query,
                    opts.batch_size,
                    Z3TaskPriority::lowest(),
                )
                .into(),
            );
        }
    }
}
