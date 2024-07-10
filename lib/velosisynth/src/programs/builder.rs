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

//! Synthesis Module: Operations

use indexmap::IndexMap;
use std::iter::Peekable;
use std::sync::Arc;
use std::vec::IntoIter;

use itertools::{Itertools, MultiProduct};

use crate::opts::SynthOpts;
use crate::programs::ProgramActions;

use super::{Expression, FieldActions, FieldOp, FieldSliceOp, Literal, Program};

#[derive(Default)]
pub struct ProgramsIter {
    // ///
    // expr: Vec<Arc<Expression>>,
    pub programs: Vec<Peekable<MultiProduct<IntoIter<ProgramActions>>>>,
    pub stat_max_programs: u128,
    pub stat_num_programs: u128,
}

impl ProgramsIter {
    pub fn new_noop() -> Self {
        Self {
            programs: vec![vec![vec![ProgramActions::Noop]]
                .into_iter()
                .multi_cartesian_product()
                .peekable()],
            stat_num_programs: 1,
            stat_max_programs: 1,
        }
    }

    pub fn next_program(&mut self) -> Option<Program> {
        let last = self.programs.last_mut()?;
        let next = last.next();
        if let Some(actions) = next {
            self.stat_num_programs += 1;
            let p = Program(actions);
            return Some(p);
        }

        self.programs.pop();
        let last = self.programs.last_mut()?;
        if let Some(actions) = last.next() {
            self.stat_num_programs += 1;
            let p = Program(actions);
            return Some(p);
        }
        None
    }

    pub fn has_programs(&mut self) -> bool {
        if let Some(last) = self.programs.last_mut() {
            last.peek().is_some()
        } else {
            false
        }
    }
}

pub struct ProgramsBuilder {
    /// the fields we have
    #[allow(clippy::type_complexity)]
    fields: IndexMap<Arc<String>, Vec<(Arc<String>, u64, usize)>>,
    /// the instructions we can execute
    instructions: Vec<Arc<String>>,
    /// variables we can chose from, plus the implicit flags variable
    vars: Vec<Arc<String>>,
    /// some flags to chose from
    flags: Vec<(Arc<String>, Arc<String>)>,
    /// the translation range has a lower limit
    has_limit: bool,
    /// has a limit expression
    has_limit_expression: bool,
    /// the unit has a fixed sized translation range
    fixed_size: bool,
    /// the unit has a fixed sized translation range
    fixed_vaddr: bool,
}

impl ProgramsBuilder {
    pub fn new() -> Self {
        Self {
            fields: IndexMap::new(),
            vars: vec![],
            flags: vec![],
            instructions: vec![],
            has_limit: false,
            has_limit_expression: false,
            fixed_size: false,
            fixed_vaddr: false,
        }
    }

    // whether there are any programs
    pub fn has_programs(&self) -> bool {
        !self.fields.is_empty()
    }

    pub fn set_limit(&mut self) -> &mut Self {
        self.has_limit = true;
        self
    }

    pub fn set_limit_expression(&mut self) -> &mut Self {
        self.has_limit_expression = true;
        self
    }

    pub fn set_fixed_size(&mut self) -> &mut Self {
        self.fixed_size = true;
        self
    }
    pub fn set_fixed_vaddr(&mut self) -> &mut Self {
        self.fixed_vaddr = true;
        self
    }

    /// adds a field slice to the builder
    pub fn add_field_slice(
        &mut self,
        field: &str,
        slice: &str,
        start: u64,
        bits: usize,
    ) -> &mut Self {
        self.fields
            .entry(Arc::new(field.to_string()))
            .or_default()
            .push((Arc::new(slice.to_string()), start, bits));
        self
    }

    /// adds a full field to the builder
    pub fn add_field(&mut self, field: String) -> &mut Self {
        //let slices = slices.into_iter().map(|(s, b)| (Arc::new(s), b)).collect();
        self.fields.insert(Arc::new(field), Vec::new());
        self
    }

    /// adds the possible flags to the builder
    pub fn add_flags(&mut self, var: Arc<String>, flag: String) -> &mut Self {
        self.flags.push((var, Arc::new(flag)));
        self
    }

    pub fn add_instruction(&mut self, instr: String) -> &mut Self {
        self.instructions.push(Arc::new(instr));
        self
    }

    // adds a variable to the builder
    pub fn add_var(&mut self, var: String) -> &mut Self {
        let var = Arc::new(var);
        if !self.vars.contains(&var) {
            self.vars.push(var);
        }
        self
    }

    /// Constructs all possible expressions with the literals
    fn construct_expressions(&self, _opts: &SynthOpts) -> Vec<Arc<Expression>> {
        // TODO: probably should filter this based on size...

        // macro to generate terminal parsers for operator tokens.
        macro_rules! expr_combinator1 (($vec:ident, $expr: expr, $vars:ident, $vals:ident) => (
            for val in &$vals {
                $vec.push(Arc::new($expr(val.clone())));
            }
            for var in &$vars {
                $vec.push(Arc::new($expr(var.clone())));
            }
        ));

        // macro to generate terminal parsers for operator tokens.
        macro_rules! expr_combinator2 (($vec:ident, $expr: expr, $vars:ident, $vals:ident) => (
            for val in &$vals {
                for var in &$vars {
                    $vec.push(Arc::new($expr(Arc::new(Expression::Lit(var.clone())), val.clone())));
                }
            }
        ));

        // hold the created expressions
        let mut expr = Vec::new();

        // all varaible literals
        // let vars: Vec<Literal> = self.vars.iter().map(|v| Literal::Var(v.clone())).collect();
        let vars: Vec<Literal> = self
            .vars
            .iter()
            .filter_map(|v| {
                let filter =
                    self.fixed_size && v.as_str() == "sz" || self.fixed_vaddr && v.as_str() == "va";
                if filter {
                    None
                } else {
                    Some(Literal::Var(v.clone()))
                }
            })
            .collect();

        // add literals
        let vals = vec![Literal::Val(1), Literal::Val(0)];
        expr_combinator1!(expr, Expression::Lit, vars, vals);

        // add the binary operation expressions over 1
        let vals = vec![Literal::Val(1)];
        expr_combinator2!(expr, Expression::Add, vars, vals);
        expr_combinator2!(expr, Expression::Sub, vars, vals);
        // expr_combinator2!(expr, Expression::And, vars, vals);
        // expr_combinator2!(expr, Expression::Or, vars, vals);

        let mut add_expr = None;
        if self.has_limit && !self.has_limit_expression {
            // println!("adding (va + sz) and va+sz - 1");
            for var1 in &vars {
                for var2 in &vars {
                    if let (Literal::Var(v1), Literal::Var(v2)) = (var1, var2) {
                        if v1.as_str() == "va" && v2.as_str() == "sz" {
                            let e = Arc::new(Expression::Add(
                                Arc::new(Expression::Lit(var1.clone())),
                                var2.clone(),
                            ));
                            add_expr = Some(e.clone());
                            expr.push(e.clone());
                            expr.push(Arc::new(Expression::Sub(e, Literal::Val(1))));
                        }
                    }
                }
            }
        }

        // the flags, it's either a flag or not a flag
        for (v, f) in &self.flags {
            expr.push(Arc::new(Expression::Lit(Literal::Flag(
                v.clone(),
                f.clone(),
            ))));
            expr.push(Arc::new(Expression::Not(Literal::Flag(
                v.clone(),
                f.clone(),
            ))));
        }

        for var in &vars {
            expr.push(Arc::new(Expression::ShiftMask(
                Arc::new(Expression::Lit(var.clone())),
                Literal::Num,
                Literal::Num,
            )));
        }
        // shift mask operators over the va + sz expression
        if let Some(e) = add_expr.as_ref() {
            // println!("adding (va + sz) and va+sz - 1 shift and mask");
            expr.push(Arc::new(Expression::ShiftMask(
                e.clone(),
                Literal::Num,
                Literal::Num,
            )));
            expr.push(Arc::new(Expression::ShiftMask(
                Arc::new(Expression::Sub(e.clone(), Literal::Val(1))),
                Literal::Num,
                Literal::Num,
            )));
        }

        // possible values with
        // let vals = vec![Literal::Num];
        // expr_combinator1!(expr, Expression::Lit, vars, vals);
        // expr_combinator2!(expr, Expression::Add, vars, vals);
        // expr_combinator2!(expr, Expression::Sub, vars, vals);
        // expr_combinator2!(expr, Expression::And, vars, vals);
        // expr_combinator2!(expr, Expression::Or, vars, vals);

        // put the multiply stuff at the end
        // let just_num = vec![Literal::Num];
        // expr_combinator2!(expr, Expression::Mul, vars, just_num);
        // expr_combinator2!(expr, Expression::Div, vars, just_num);

        // and we're done
        expr
    }

    /// constructs new programs
    pub fn into_iter(&mut self, opts: &SynthOpts) -> ProgramsIter {
        // get all the expression possibilities;
        let exprs = self.construct_expressions(opts);

        log::info!(
            target : "[ProgramsBuilder]", "Build programs: {} fields, {} slices, {} vars, {} flags, {} expr",
            self.fields.len(),
            self.fields.iter().map(|a| a.1.len()).sum::<usize>(),
            self.vars.len(),
            self.flags.len(),
            exprs.len()
        );

        log::info!(target : "[ProgramsBuilder]", " * Vars: {:?}", self.vars);
        log::info!(target : "[ProgramsBuilder]", " * Flags: {:?}", self.flags);
        log::info!(target : "[ProgramsBuilder]", " * Fields: {:?}", self.fields);
        log::info!(target : "[ProgramsBuilder]", " * Instructions: {:?}", self.instructions);

        log::debug!(target : "[ProgramsBuilder]", " * Expressions:");
        for (i, e) in exprs.iter().enumerate() {
            log::debug!(target : "[ProgramsBuilder]", "    - e{}: {:?}", i, e);
        }

        // start with the instructions so we can do the length 1 programs.
        // we may just use a subset of the programs, and there may be multiple fields that
        // change the same program state, so let's do the powerset the fields here.
        let base_programs = self
            .fields
            .iter()
            .map(|f| ProgramActions::FieldActions(Arc::new(FieldActions(f.0.clone(), Vec::new()))))
            .powerset();
        let instructions = self
            .instructions
            .iter()
            .map(|f| ProgramActions::Instruction(f.clone()))
            .powerset();

        // create permutations of the programs, in case we have multiple fields, the order may
        // matter here.
        let mut permuted_base_programs = Vec::new();
        for prog in base_programs {
            let len = prog.len();
            for perm in prog.into_iter().permutations(len).unique() {
                permuted_base_programs.push(perm);
            }
        }

        // create permutations of the instructions, in case we have multiple instructions, the order may
        // matter here.
        let mut permuted_instructions = Vec::new();
        for instr in instructions {
            let len = instr.len();
            for perm in instr.into_iter().permutations(len).unique() {
                permuted_instructions.push(perm);
            }
        }

        // now we have a sequence of base programs and a sequence of instructions that we can
        // combine in any possible way.
        let mut big_step_programs = Vec::new();
        for prog in permuted_base_programs.iter() {
            for instr in permuted_instructions.iter() {
                if prog.is_empty() {
                    if !instr.is_empty() {
                        big_step_programs.push(instr.clone());
                    }
                    continue;
                }

                if instr.is_empty() {
                    big_step_programs.push(prog.clone());
                    continue;
                }

                // add the instruction last
                let mut current_prog = Vec::with_capacity(prog.len() + instr.len());
                current_prog.extend(prog.clone());
                current_prog.extend(instr.clone());
                big_step_programs.push(current_prog);

                // now add the remaining instructions at various places
                // println!("Combining: {prog:?} and {instr:?}");
                for i in 0..prog.len() {
                    let mut current_prog = Vec::with_capacity(prog.len() + instr.len());
                    current_prog.extend(prog[0..i].iter().cloned());
                    current_prog.extend(instr.clone());
                    current_prog.extend(prog[i..].iter().cloned());

                    big_step_programs.push(current_prog);
                }
            }
        }

        // println!("Big Step Programs: {big_step_programs:?}");

        // now for each field we build all possible values...

        let init_zero = FieldOp::InsertField(Arc::new(Expression::Lit(Literal::Val(0))));
        let init_read = FieldOp::ReadAction;

        let mut field_programs = IndexMap::new();
        let mut field_programs_stat = IndexMap::new();
        for (field, slices) in self.fields.iter_mut() {
            // sort the slices
            slices.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

            // there were no slices in the field, simply construct the programs with all the
            if slices.is_empty() {
                let mut field_ops = Vec::with_capacity(exprs.len() * 2);
                for expr in &exprs {
                    let expr = FieldOp::InsertField(expr.clone());
                    field_ops.push(Arc::new(FieldActions(
                        field.clone(),
                        vec![init_read.clone(), expr.clone()],
                    )));
                    field_ops.push(Arc::new(FieldActions(
                        field.clone(),
                        vec![init_zero.clone(), expr],
                    )));
                }
                field_programs_stat.insert(field.clone(), field_ops.len() as u128);
                field_programs.insert(field.clone(), field_ops);
                continue;
            }

            field_programs.insert(field.clone(), Vec::new());

            // construct the powerset of all possible field operations
            for slices_list in &[slices] {
                // slices.iter().powerset() {
                let slice_exprs: Vec<_> = slices_list
                    .iter()
                    .filter_map(|slice| {
                        let slice_expr: Vec<_> = exprs
                            .iter()
                            .filter_map(|expr| {
                                if !expr.skip_for_bits(slice.2) || opts.disable_expr_opt {
                                    Some(FieldSliceOp(slice.0.clone(), expr.clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();

                        if !slice_expr.is_empty() {
                            Some(slice_expr)
                        } else {
                            None
                        }
                    })
                    .collect();

                let num = 2 * slice_exprs
                    .iter()
                    .map(|l| l.len() as u128)
                    .product::<u128>();
                field_programs_stat.insert(field.clone(), num);

                if opts.disable_program_generation {
                    continue;
                }

                let mut field_ops =
                    Vec::with_capacity(slice_exprs.iter().map(|s| s.len()).sum::<usize>());
                for slice_expr in slice_exprs.into_iter().multi_cartesian_product() {
                    field_ops.push(Arc::new(FieldActions(
                        field.clone(),
                        vec![
                            init_zero.clone(),
                            FieldOp::InsertFieldSlices(slice_expr.clone()),
                        ],
                    )));
                    field_ops.push(Arc::new(FieldActions(
                        field.clone(),
                        vec![init_read.clone(), FieldOp::InsertFieldSlices(slice_expr)],
                    )));
                }
                field_programs.get_mut(field).unwrap().extend(field_ops);
            }
        }

        // now we have all the possible programs for each field and the field programs. We can no
        // combine them to get the final programs.
        let mut programs = Vec::new();
        let mut stat_max_programs = 0;
        for big_step_program in big_step_programs {
            // get
            // convert into iterators.
            stat_max_programs += big_step_program
                .iter()
                .map(|program_actions| match program_actions {
                    ProgramActions::FieldActions(f) => *field_programs_stat.get(&f.0).unwrap(),
                    _p => 1u128,
                })
                .product::<u128>();

            let program_parts: Vec<_> = if opts.disable_program_generation {
                vec![vec![ProgramActions::Noop]]
            } else {
                big_step_program
                    .into_iter()
                    .map(|program_actions| match program_actions {
                        ProgramActions::FieldActions(f) => field_programs
                            .get(&f.0)
                            .unwrap()
                            .iter()
                            .map(|p| ProgramActions::FieldActions(p.clone()))
                            .collect(),
                        p => vec![p],
                    })
                    .collect()
            };

            programs.push(
                program_parts
                    .into_iter()
                    .multi_cartesian_product()
                    .peekable(),
            );
        }

        log::info!(target : "[ProgramsBuilder]", "constructed {} programs", stat_max_programs);

        programs.reverse();

        ProgramsIter {
            programs,
            stat_num_programs: 0,
            stat_max_programs,
        }
    }
}

impl Default for ProgramsBuilder {
    fn default() -> Self {
        Self::new()
    }
}
