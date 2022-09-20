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
use std::ops::Deref;
use std::sync::Arc;

use smt2::{Function, Smt2Context, Term, VarBinding, VarDecl};

use crate::ast::Param;

use super::types;

/// the arguments are for either a symbolic variable (num) or a variable (var)
#[derive(Debug, Clone, PartialEq, Eq)]
enum ArgX {
    /// a constant number
    Num,
    /// the value zero
    Zero,
    /// the value one
    One,
    /// a variable
    Var(Arc<String>),
}

#[derive(Debug)]
struct FieldSliceOp(Arc<String>, ArgX);

/// a field operation is either inserting a value into a field or its slice, or reading it
#[derive(Debug)]
pub enum FieldOps {
    InsertField(ArgX),
    InsertFieldSlices(Vec<FieldSliceOp>),
    ReadAction,
}

/// a field ops is a list of operations on a given field,
#[derive(Debug)]
struct FieldOperations(Arc<String>, Arc<FieldOps>);

/// the operations are a vector of field ops
pub struct Program {
    ops: Vec<Arc<FieldOperations>>,
}

pub struct SymbolicVars {
    counter: usize,
}

impl SymbolicVars {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn next(&mut self) -> String {
        let name = format!("symvar!{}", self.counter);
        self.counter += 1;
        name
    }

    pub fn add_to_context(&self, smt: &mut Smt2Context) {
        smt.comment("Variable Definitions".to_string());
        for i in 0..self.counter {
            let name = format!("symvar!{}", i);
            smt.variable(VarDecl::new(name, types::num()));
        }
    }

    pub fn add_get_values(&self, smt: &mut Smt2Context) {
        smt.comment("Get Values".to_string());
        if self.counter == 0 {
            smt.echo("()".to_string());
            return;
        }
        let mut terms = Vec::new();
        for i in 0..self.counter {
            let name = format!("symvar!{}", i);
            terms.push(Term::ident(name));
        }

        smt.get_value(terms);
    }
}

impl Program {
    pub fn to_smt2(&self, fnname: &str, args: &[Param]) -> (Smt2Context, SymbolicVars) {
        let mut smt = Smt2Context::new();

        let mut smtops = Vec::new();

        let mut symvar = SymbolicVars::new();
        for fops in self.ops.iter() {
            match fops.1.deref() {
                FieldOps::InsertField(arg) => {
                    let arg = match arg {
                        ArgX::Num => symvar.next(),
                        ArgX::Zero => "#x0000000000000000".to_string(),
                        ArgX::One => "#x0000000000000001".to_string(),
                        ArgX::Var(v) => format!("{}", v),
                    };
                    let fname = format!("Model.IFace.{}.set", fops.0);
                    smtops.push((fname, Some(arg)));
                }
                FieldOps::InsertFieldSlices(sliceops) => {
                    for sliceop in sliceops.iter() {
                        let arg = match &sliceop.1 {
                            ArgX::Num => symvar.next(),
                            ArgX::Zero => "#x0000000000000000".to_string(),
                            ArgX::One => "#x0000000000000001".to_string(),
                            ArgX::Var(v) => format!("{}", v),
                        };
                        let fname = format!("Model.IFace.{}.{}.set", fops.0, sliceop.0);
                        smtops.push((fname, Some(arg)));
                    }
                }
                FieldOps::ReadAction => {
                    let fname = format!("Model.IFace.{}.readaction ", fops.0);
                    smtops.push((fname, None));
                }
            }

            let fname = format!("Model.IFace.{}.writeaction ", fops.0);
            smtops.push((fname, None));
        }

        println!("smtops: {:?}", smtops);
        // define the variables
        symvar.add_to_context(&mut smt);

        let mut f = Function::new(fnname.to_string(), String::from("Model_t"));
        f.add_arg(String::from("st"), types::model());
        for arg in args.iter() {
            f.add_arg(arg.name.clone(), types::type_to_smt2(&arg.ptype));
        }

        let mut defs = Vec::new();
        let mut stvar = String::from("st");

        for (i, (f, a)) in smtops.drain(..).enumerate() {
            let newvar = format!("st_{}", i + 1);

            let m = Term::ident(stvar.clone());

            let fcall = match a {
                Some(a) => Term::fn_apply(f, vec![m, Term::ident(a)]),
                None => Term::fn_apply(f, vec![m]),
            };

            defs.push(VarBinding::new(newvar.clone(), fcall));
            stvar = newvar;
        }

        let body = defs.iter().rev().fold(Term::ident(stvar), |acc, x| {
            Term::letexpr(vec![x.clone()], acc)
        });

        f.add_body(body);
        smt.function(f);

        (smt, symvar)
    }
}

pub struct ProgramsBuilder {
    /// the fields we have
    fields: HashMap<Arc<String>, Vec<Arc<String>>>,
    /// variables we can chose from, plus the implicit flags variable
    vars: Vec<Arc<String>>,
}

impl ProgramsBuilder {
    pub fn new() -> Self {
        Self {
            fields: HashMap::new(),
            vars: vec![],
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

    // adds a full field to the builder
    pub fn add_field(&mut self, field: String, slices: Vec<String>) -> &mut Self {
        let slices = slices.into_iter().map(|s| Arc::new(s)).collect();
        self.fields.insert(Arc::new(field), slices);
        self
    }

    // adds a variable to the builder
    pub fn add_var(&mut self, var: String) -> &mut Self {
        self.vars.push(Arc::new(var));
        self
    }

    pub fn construct_programs(&self, symbolic: bool) -> Vec<Program> {
        // a vector with an entry for each field that contains a vector for
        // all possible operations on this field
        let mut field_operations: Vec<Vec<Arc<FieldOperations>>> = Vec::new();

        // now we loop over each field and slices to construct all possible operations
        for (field, slices) in &self.fields {
            // all programs that operate on the slices of this field
            let mut slice_programs: Vec<Vec<ArgX>> = slices.iter().map(|op| vec![]).collect();
            for slice in slices {
                // the new slice programs we've generated
                let mut new_slice_programs = Vec::new();

                // extend all programs by adding the variables
                for program in &slice_programs {
                    if !symbolic {
                        for var in &self.vars {
                            let mut program_new = program.clone();
                            program_new.push(ArgX::Var(var.clone()));
                            new_slice_programs.push(program_new);
                        }
                        let mut program_new = program.clone();
                        program_new.push(ArgX::One);
                        new_slice_programs.push(program_new);

                        let mut program_new = program.clone();
                        program_new.push(ArgX::Zero);
                        new_slice_programs.push(program_new);
                    } else {
                        // add the constant number as well
                        let mut program_new = program.clone();
                        program_new.push(ArgX::Num);
                        new_slice_programs.push(program_new);
                    }
                }
                // set them as the current programs
                slice_programs = new_slice_programs;
            }

            // now we construct the programs to manipulate the fields
            let mut field_programs = Vec::new();
            for mut program in slice_programs.drain(..) {
                let mut sliceops = Vec::new();
                for (i, slice) in slices.iter().enumerate() {
                    sliceops.push(FieldSliceOp(slice.clone(), program.pop().unwrap()));
                }

                field_programs.push(Arc::new(FieldOps::InsertFieldSlices(sliceops)));
            }

            // add full field accesses as well
            // for var in &self.vars {
            //     field_programs.push(Arc::new(FieldOps::InsertField(ArgX::Var(var.clone()))));
            // }
            // field_programs.push(Arc::new(FieldOps::InsertField(ArgX::Num)));

            // now add the variants to modify the build to the field operations
            let ops = field_programs
                .into_iter()
                .map(|p| Arc::new(FieldOperations(field.clone(), p)))
                .collect();
            field_operations.push(ops);
        }

        // now build any possible compinatins of the programs

        let mut programs: Vec<Vec<Arc<FieldOperations>>> =
            self.fields.iter().map(|op| vec![]).collect();

        // we need to do something for each program
        for fops in field_operations {
            let mut prog_new = Vec::new();
            for program in programs {
                for fop in &fops {
                    let mut program_new = program.clone();
                    program_new.push(fop.clone());
                    prog_new.push(program_new);
                }
            }
            programs = prog_new;
        }

        // and conver the programs into the final format
        programs.into_iter().map(|p| Program { ops: p }).collect()
    }
}
