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

pub struct ProgramsBuilder {
    /// the fields we have
    fields: HashMap<Arc<String>, Vec<Arc<String>>>,
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

    /// adds a field slice to the builder
    pub fn add_field_slice(&mut self, field: &str, slice: &str) -> &mut Self {
        self.fields
            .entry(Arc::new(field.to_string()))
            .or_insert(vec![])
            .push(Arc::new(slice.to_string()));
        self
    }

    /// adds a full field to the builder
    pub fn add_field(&mut self, field: String, slices: Vec<String>) -> &mut Self {
        let slices = slices.into_iter().map(Arc::new).collect();
        self.fields.insert(Arc::new(field), slices);
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
    pub fn construct_expressions(&self) -> Vec<Arc<Expression>> {
        // all possible value literals
        let vals = vec![Literal::Val(1), Literal::Val(0), Literal::Num];

        // all varaible literals
        let vars: Vec<Literal> = self.vars.iter().map(|v| Literal::Var(v.clone())).collect();

        let mut expr = Vec::new();

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
                    $vec.push(Arc::new($expr(val.clone(), var.clone())));
                }
            }
        ));

        // unary expressions
        expr_combinator1!(expr, Expression::Lit, vars, vals);
        expr_combinator1!(expr, Expression::Not, vars, vals);

        // binary expressions
        expr_combinator2!(expr, Expression::RShift, vars, vals);
        expr_combinator2!(expr, Expression::LShift, vars, vals);
        expr_combinator2!(expr, Expression::Div, vars, vals);
        expr_combinator2!(expr, Expression::Mul, vars, vals);
        expr_combinator2!(expr, Expression::Add, vars, vals);
        expr_combinator2!(expr, Expression::Sub, vars, vals);
        expr_combinator2!(expr, Expression::And, vars, vals);
        expr_combinator2!(expr, Expression::LShift, vars, vals);
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

        // and we're done
        expr
    }

    /// constructs new programs
    pub fn construct_new_programs(&self) -> Vec<Program> {
        // get all the expression possibilities;
        let exprs = self.construct_expressions();

        let mut fieldprograms = Vec::new();

        // a program must have some choice of things for each of the fields
        for (field, slices) in &self.fields {
            let mut fieldops = Vec::with_capacity(exprs.len() * (1 + slices.len()));

            // the read / write actions
            fieldops.push(FieldOp::ReadAction);
            // field_progs.push(FieldOp::WriteAction);

            // write the entire field
            for expr in &exprs {
                fieldops.push(FieldOp::InsertField(expr.clone()))
            }

            // we now build a combination of all expressions with all slices
            let mut it = MultiDimIterator::new(slices.len(), exprs.len());
            while let Some(conf) = it.next() {
                let mut sliceops = Vec::new();
                for (i, e) in conf.iter().enumerate() {
                    sliceops.push(FieldSliceOp(slices[i].clone(), exprs[*e].clone()));
                }

                fieldops.push(FieldOp::InsertFieldSlices(sliceops));
            }

            // field ops now has all the possible field operations, programs of size 1
            let mut fieldprogs = Vec::with_capacity(fieldops.len());
            for op in &fieldops {
                fieldprogs.push(Arc::new(FieldActions(field.clone(), vec![op.clone()])));
            }

            // programs of length 2
            for (i, op1) in fieldops.iter().enumerate() {
                for (j, op2) in fieldops.iter().enumerate() {
                    // twice the same action
                    if i == j {
                        continue;
                    }

                    // that would mean we overwrite the field slices inserted...
                    if op2.would_overwrite(op1) {
                        continue;
                    }

                    fieldprogs.push(Arc::new(FieldActions(
                        field.clone(),
                        vec![op1.clone(), op2.clone()],
                    )));
                }
            }

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

        programs
    }

    // pub fn construct_programs(&self, symbolic: bool) -> Vec<Program> {
    //     // a vector with an entry for each field that contains a vector for
    //     // all possible operations on this field
    //     let mut field_operations: Vec<Vec<Arc<FieldActions>>> = Vec::new();
    //     let mut field_operations_2: Vec<Vec<Arc<FieldActions>>> = Vec::new();

    //     // TODO: Revisit this!

    //     // now we loop over each field and slices to construct all possible operations
    //     for (field, slices) in &self.fields {
    //         // all programs that operate on the slices of this field
    //         let mut slice_programs: Vec<Vec<Expression>> = slices.iter().map(|_| vec![]).collect();
    //         for _slice in slices {
    //             // the new slice programs we've generated
    //             let mut new_slice_programs = Vec::new();

    //             // extend all programs by adding the variables
    //             for program in &slice_programs {
    //                 if !symbolic {
    //                     // add one
    //                     let mut program_new = program.clone();
    //                     program_new.push(Expression::Lit(Literal::Val(1)));
    //                     new_slice_programs.push(program_new);

    //                     // add zero
    //                     let mut program_new = program.clone();
    //                     program_new.push(Expression::Lit(Literal::Val(0)));
    //                     new_slice_programs.push(program_new);

    //                     for var in &self.vars {
    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Lit(Literal::Var(var.clone())));
    //                         new_slice_programs.push(program_new);
    //                     }

    //                     for (v, f) in &self.flags {
    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Lit(Literal::Flag(v.clone(), f.clone())));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Not(Literal::Flag(v.clone(), f.clone())));
    //                         new_slice_programs.push(program_new);
    //                     }
    //                 } else {
    //                     // add the constant number as well
    //                     let mut program_new = program.clone();
    //                     program_new.push(Expression::Lit(Literal::Num));
    //                     new_slice_programs.push(program_new);

    //                     for var in &self.vars {
    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Lit(Literal::Var(var.clone())));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::RShift(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::ShiftMask(
    //                             Literal::Var(var.clone()),
    //                             Literal::Num,
    //                             Literal::Num,
    //                         ));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::Add(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::Sub(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::Mul(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);

    //                         // let mut program_new = program.clone();
    //                         // program_new.push(Expression::Div(Literal::Var(var.clone()), Literal::Num));
    //                         // new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::And(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new
    //                             .push(Expression::Or(Literal::Var(var.clone()), Literal::Num));
    //                         new_slice_programs.push(program_new);
    //                     }

    //                     for (v, f) in &self.flags {
    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Lit(Literal::Flag(v.clone(), f.clone())));
    //                         new_slice_programs.push(program_new);

    //                         let mut program_new = program.clone();
    //                         program_new.push(Expression::Not(Literal::Flag(v.clone(), f.clone())));
    //                         new_slice_programs.push(program_new);
    //                     }
    //                 }
    //             }
    //             // set them as the current programs
    //             slice_programs = new_slice_programs;
    //         }

    //         // now we construct the programs to manipulate the fields
    //         let mut field_programs = Vec::new();
    //         //field_programs.push(Arc::new(FieldOp::ReadAction));
    //         field_programs.push(Arc::new(FieldOp::InsertField(Expression::Arg(
    //             Literal::Zero,
    //         ))));

    //         for mut program in slice_programs.drain(..) {
    //             let mut sliceops = Vec::new();
    //             for (_i, slice) in slices.iter().enumerate() {
    //                 sliceops.push(FieldSliceOp(slice.clone(), program.pop().unwrap()));
    //             }

    //             field_programs.push(Arc::new(FieldOp::InsertFieldSlices(sliceops)));
    //         }

    //         // add full field accesses as well
    //         // for var in &self.vars {
    //         //     field_programs.push(Arc::new(FieldOp::InsertField(Literal::Var(var.clone()))));
    //         // }

    //         // now add the variants to modify the build to the field operations
    //         let ops = field_programs
    //             .iter()
    //             .map(|p| Arc::new(FieldActions(field.clone(), vec![p.clone()])))
    //             .collect();

    //         field_operations.push(ops);

    //         let ops = field_programs
    //             .into_iter()
    //             .map(|p| {
    //                 Arc::new(FieldActions(
    //                     field.clone(),
    //                     vec![Arc::new(FieldOp::ReadAction), p],
    //                 ))
    //             })
    //             .collect();

    //         field_operations_2.push(ops);
    //     }

    //     // now build any possible compinatins of the programs

    //     let mut final_programs = Vec::new();

    //     // we need to do something for each program

    //     let mut programs: Vec<Vec<Arc<FieldActions>>> =
    //         self.fields.iter().map(|_| vec![]).collect();

    //     for fops in field_operations {
    //         let mut prog_new = Vec::new();
    //         for program in programs {
    //             for fop in &fops {
    //                 let mut program_new = program.clone();
    //                 program_new.push(fop.clone());
    //                 prog_new.push(program_new);
    //             }
    //         }
    //         programs = prog_new;
    //     }

    //     final_programs.extend(programs);

    //     let mut programs: Vec<Vec<FieldActions>> =
    //         self.fields.iter().map(|_| vec![]).collect();

    //     for fops in field_operations_2 {
    //         let mut prog_new = Vec::new();
    //         for program in programs {
    //             for fop in &fops {
    //                 let mut program_new = program.clone();
    //                 program_new.push(fop.clone());
    //                 prog_new.push(program_new);
    //             }
    //         }
    //         programs = prog_new;
    //     }

    //     final_programs.extend(programs);

    //     // and conver the programs into the final format
    //     final_programs
    //         .into_iter()
    //         .map(|p| Program(p))
    //         .collect()
    // }
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
struct MultiDimIterator {
    maxvals: Vec<usize>,
    current: Vec<usize>,
    done: bool,
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
        }
    }

    pub fn next(&mut self) -> Option<&[usize]> {
        if self.done {
            return None;
        }

        let mut carry = true;
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
        if carry {
            self.done = true;
            None
        } else {
            Some(self.current.as_slice())
        }
    }
}
