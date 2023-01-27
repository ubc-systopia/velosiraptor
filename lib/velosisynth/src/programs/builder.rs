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

use std::collections::HashMap;
use std::sync::Arc;

use super::{Expression, FieldActions, FieldOp, FieldSliceOp, Literal, Program};

pub struct ProgramsIter {
    // ///
    // expr: Vec<Arc<Expression>>,
    pub programs: Vec<Program>,
}

impl ProgramsIter {
    pub fn next_program(&mut self) -> Option<Program> {
        self.programs.pop()
    }

    pub fn has_programs(&self) -> bool {
        !self.programs.is_empty()
    }
}

pub struct ProgramsBuilder {
    /// the fields we have
    fields: HashMap<Arc<String>, Vec<(Arc<String>, usize)>>,
    /// variables we can chose from, plus the implicit flags variable
    vars: Vec<Arc<String>>,
    /// some flags to chose from
    flags: Vec<(Arc<String>, Arc<String>)>,
}

impl ProgramsBuilder {
    pub fn new() -> Self {
        Self {
            fields: HashMap::new(),
            vars: vec![],
            flags: vec![],
        }
    }

    // whether there are any programs
    pub fn has_programs(&self) -> bool {
        !self.fields.is_empty()
    }

    /// adds a field slice to the builder
    pub fn add_field_slice(&mut self, field: &str, slice: &str, bits: usize) -> &mut Self {
        self.fields
            .entry(Arc::new(field.to_string()))
            .or_default()
            .push((Arc::new(slice.to_string()), bits));
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

    // adds a variable to the builder
    pub fn add_var(&mut self, var: String) -> &mut Self {
        self.vars.push(Arc::new(var));
        self
    }

    /// Constructs all possible expressions with the literals
    fn construct_expressions(&self) -> Vec<Arc<Expression>> {
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
                    $vec.push(Arc::new($expr(var.clone(), val.clone())));
                }
            }
        ));

        // hold the created expressions
        let mut expr = Vec::new();

        // all varaible literals
        let vars: Vec<Literal> = self.vars.iter().map(|v| Literal::Var(v.clone())).collect();

        // all possible value literals
        // let vals = vec![Literal::Val(1), Literal::Val(0), Literal::Num];
        let vals = vec![Literal::Num];

        // unary expressions
        expr_combinator1!(expr, Expression::Lit, vars, vals);
        // not is not valid for numbers, we don't have neg
        // expr_combinator1!(expr, Expression::Not, vars, vals);

        // updated value literals
        // let vals = vec![Literal::Val(1), Literal::Num];
        let vals = vec![Literal::Num];

        // binary expressions
        //expr_combinator2!(expr, Expression::RShift, vars, vals);
        expr_combinator2!(expr, Expression::LShift, vars, vals);
        expr_combinator2!(expr, Expression::Add, vars, vals);
        expr_combinator2!(expr, Expression::Sub, vars, vals);
        expr_combinator2!(expr, Expression::And, vars, vals);
        expr_combinator2!(expr, Expression::Or, vars, vals);

        // the shiftmask operators
        for val1 in &vals {
            for var in &vars {
                for val2 in &vals {
                    expr.push(Arc::new(Expression::ShiftMask(
                        var.clone(),
                        val1.clone(),
                        val2.clone(),
                    )));
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

        // put the multiply stuff at the end
        let just_num = vec![Literal::Num];
        expr_combinator2!(expr, Expression::Mul, vars, just_num);
        // expr_combinator2!(expr, Expression::Div, vars, just_num);

        // and we're done
        expr
    }

    /// constructs new programs
    pub fn construct_new_programs(&mut self) -> Vec<Program> {
        // get all the expression possibilities;
        let exprs = self.construct_expressions();

        log::info!(
            target : "[ProgramsBuilder]", "build programs: {} fields, {} slices, {} vars, {} flags, {} expr",
            self.fields.len(),
            self.fields.iter().map(|a| a.1.len()).sum::<usize>(),
            self.vars.len(),
            self.flags.len(),
            exprs.len()
        );

        log::debug!(target : "[ProgramsBuilder]", "Vars: {:?}", self.vars);
        log::debug!(target : "[ProgramsBuilder]", "Flags: {:?}", self.flags);
        log::debug!(target : "[ProgramsBuilder]", "Fields: {:?}", self.fields);

        log::debug!(target : "[ProgramsBuilder]", "Expressions:");
        for (i, e) in exprs.iter().enumerate() {
            log::debug!(target : "[ProgramsBuilder]", "  - e{}: {:?}", i, e);
        }

        let mut fieldprograms = Vec::new();

        // a program must have some choice of things for each of the fields
        for (field, slices) in self.fields.iter_mut() {
            // sort the slices
            slices.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

            let mut fieldops = Vec::with_capacity(exprs.len() * (1 + slices.len()));

            // write the entire field,
            if slices.is_empty() {
                // we don't have any slices here, so just add the expressions
                // on the entire field
                for expr in &exprs {
                    fieldops.push(FieldOp::InsertField(expr.clone()))
                }
            } else {
                // we had slices, so just add one expression for zeroing the slice
                fieldops.push(FieldOp::InsertField(Arc::new(Expression::Lit(
                    Literal::Val(0),
                ))));
            }

            // we now build a combination of all expressions with all slices
            let mut it = MultiDimIterator::new(slices.len(), exprs.len());
            while let Some(conf) = it.next() {
                let mut sliceops = Vec::new();
                for (i, e) in conf.iter().enumerate() {
                    let (s, b) = &slices[i];
                    if exprs[*e].skip_for_bits(*b) {
                        continue;
                    }

                    // TODO: add constraints on the symvar
                    sliceops.push(FieldSliceOp(s.clone(), exprs[*e].clone()));
                }

                // we need to set every slice, so we need to to match the dimensions
                if sliceops.len() == slices.len() {
                    fieldops.push(FieldOp::InsertFieldSlices(sliceops));
                }
            }

            // the read / write actions
            fieldops.push(FieldOp::ReadAction);
            // field_progs.push(FieldOp::WriteAction);

            // field ops now has all the possible field operations, programs of size 1
            let mut fieldprogs = Vec::with_capacity(fieldops.len());
            for op in &fieldops {
                fieldprogs.push(Arc::new(FieldActions(field.clone(), vec![op.clone()])));
            }

            for op in &fieldops {
                if matches!(*op, FieldOp::ReadAction | FieldOp::InsertField(_)) {
                    continue;
                }

                // zero first
                fieldprogs.push(Arc::new(FieldActions(
                    field.clone(),
                    vec![
                        FieldOp::InsertField(Arc::new(Expression::Lit(Literal::Val(0)))),
                        op.clone(),
                    ],
                )));

                // read first
                fieldprogs.push(Arc::new(FieldActions(
                    field.clone(),
                    vec![FieldOp::ReadAction, op.clone()],
                )));
            }

            // // programs of length 2
            // for (i, op1) in fieldops.iter().enumerate() {
            //     for (j, op2) in fieldops.iter().enumerate() {
            //         // twice the same action
            //         if i == j {
            //             continue;
            //         }

            //         // that would mean we overwrite the field slices inserted...
            //         if op2.would_overwrite(op1) {
            //             continue;
            //         }

            //         fieldprogs.push(Arc::new(FieldActions(
            //             field.clone(),
            //             vec![op1.clone(), op2.clone()],
            //         )));
            //     }
            // }

            fieldprograms.push(fieldprogs);
        }

        // now we have all the possible programs, combine them

        let maxvals = fieldprograms
            .iter()
            .map(|f| f.len())
            .collect::<Vec<usize>>();
        let mut it = MultiDimIterator::with_maxvals(maxvals);

        let mut programs = Vec::new();
        while let Some(conf) = it.next() {
            let mut prog = Vec::new();
            for (i, e) in conf.iter().enumerate() {
                prog.push(fieldprograms[i][*e].clone());
            }
            programs.push(Program(prog));
        }

        log::info!(target : "[ProgramsBuilder]", "constructed {} programs", programs.len());
        for (i, p) in programs.iter().enumerate() {
            log::debug!(target : "[ProgramsBuilder]", "  - p{}: {:?}", i, p);
        }

        programs
    }

    pub fn into_iter(&mut self) -> ProgramsIter {
        let mut programs = self.construct_new_programs();
        programs.reverse();
        ProgramsIter { programs }

        // // construct the expressions
        // let exprs = self.construct_expressions();

        // panic!("foobar");

        // // field programs iterator

        // let mut it = MultiDimIterator::with_maxvals(maxvals);

        // if let Some(conf) = it.next() {
        //     let mut prog = Vec::new();
        //     for (i, e) in conf.iter().enumerate() {
        //         prog.push(fieldprograms[i][*e].clone());
        //     }
        //     Some(Program(prog))
        // } else {
        //     None
        // }
    }
}

impl Default for ProgramsBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a multi-dimensional iterator
///
/// This basically implements a counter that is incremented. Each position in the value
/// has a maximum possible value it may assume. On overflow, the next position is incremented.
pub struct MultiDimIterator {
    maxvals: Vec<usize>,
    current: Vec<usize>,
    done: bool,
    idx: usize,
}

impl MultiDimIterator {
    pub fn new(ndims: usize, maxval: usize) -> Self {
        let mut maxvals = Vec::with_capacity(ndims);
        for _ in 0..ndims {
            maxvals.push(maxval);
        }
        Self::with_maxvals(maxvals)
    }

    pub fn with_maxvals(maxvals: Vec<usize>) -> Self {
        let current = maxvals.iter().map(|_| 0).collect();
        let done = maxvals.is_empty();
        Self {
            maxvals,
            current,
            done,
            idx: 0,
        }
    }

    // pub fn len(&self) -> usize {
    //     self.maxvals.iter().product()
    // }

    // pub fn idx(&self) -> usize {
    //     self.idx
    // }

    // pub fn from_slice<T>(v: &[Vec<T>]) -> Self {
    //     let maxvals = v.iter().map(|v| v.len()).collect();
    //     Self::with_maxvals(maxvals)
    // }

    pub fn next(&mut self) -> Option<&[usize]> {
        if self.done {
            return None;
        }

        let mut carry = self.idx > 0;
        if self.idx > 0 {
            for i in 0..self.maxvals.len() {
                if carry {
                    self.current[i] += 1;
                    if self.current[i] == self.maxvals[i] {
                        self.current[i] = 0;
                    } else {
                        carry = false;
                    }
                }
            }
        }
        self.idx += 1;
        if carry {
            self.done = true;
            None
        } else {
            Some(self.current.as_slice())
        }
    }
}
