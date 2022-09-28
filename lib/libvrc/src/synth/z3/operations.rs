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
use crate::synth::{OpExpr, Operation};

use super::types;

/// the arguments are for either a symbolic variable (num) or a variable (var)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgX {
    /// a constant number
    Val(u64),
    /// a symbolic constant number
    Num,
    /// the value zero
    Zero,
    /// the value one
    One,
    /// a variable
    Var(Arc<String>),
}

impl ArgX {
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        match self {
            ArgX::Num => {
                let val = vals.pop().unwrap();
                ArgX::Val(val)
            }
            _ => self.clone(),
        }
    }

    pub fn to_term(&self, symvar: &mut SymbolicVars) -> Term {
        match self {
            ArgX::Num => Term::ident(symvar.get()),
            ArgX::Zero => Term::num(0),
            ArgX::One => Term::num(1),
            ArgX::Var(v) => Term::ident(format!("{}", v)),
            ArgX::Val(v) => Term::num(*v),
        }
    }
}

impl From<&ArgX> for OpExpr {
    fn from(prog: &ArgX) -> Self {
        match prog {
            ArgX::Val(val) => OpExpr::Num(*val),
            ArgX::Num => panic!("should not happen!"),
            ArgX::Zero => OpExpr::Num(0),
            ArgX::One => OpExpr::Num(1),
            ArgX::Var(v) => OpExpr::Var(v.to_string()),
        }
    }
}

/// the arguments are for either a symbolic variable (num) or a variable (var)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgExpr {
    Arg(ArgX),
    RShift(ArgX, ArgX),
    Div(ArgX, ArgX),
    Mul(ArgX, ArgX),
    Add(ArgX, ArgX),
    Sub(ArgX, ArgX),
}

impl ArgExpr {
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        match self {
            ArgExpr::Arg(x) => ArgExpr::Arg(x.replace_symbolic_values(vals)),
            ArgExpr::RShift(a, b) => ArgExpr::RShift(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::Div(a, b) => ArgExpr::Div(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::Mul(a, b) => ArgExpr::Mul(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::Add(a, b) => ArgExpr::Add(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::Sub(a, b) => ArgExpr::Sub(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
        }
    }

    pub fn to_term(&self, symvar: &mut SymbolicVars) -> Term {
        match self {
            ArgExpr::Arg(x) => x.to_term(symvar),
            ArgExpr::RShift(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvshr(x, y)
            }
            ArgExpr::Div(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvdiv(x, y)
            }
            ArgExpr::Mul(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvmul(x, y)
            }
            ArgExpr::Add(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvadd(x, y)
            }
            ArgExpr::Sub(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvsub(x, y)
            }
        }
    }
}

impl From<&ArgExpr> for OpExpr {
    fn from(prog: &ArgExpr) -> Self {
        match prog {
            ArgExpr::Arg(x) => OpExpr::from(x),
            ArgExpr::RShift(x, y) => {
                OpExpr::Shr(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y)))
            }
            ArgExpr::Div(x, y) => OpExpr::Div(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ArgExpr::Mul(x, y) => OpExpr::Mul(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ArgExpr::Add(x, y) => OpExpr::Add(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ArgExpr::Sub(x, y) => OpExpr::Sub(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FieldSliceOp(Arc<String>, ArgExpr);

impl FieldSliceOp {
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> FieldSliceOp {
        FieldSliceOp(self.0.clone(), self.1.replace_symbolic_values(vals))
    }
}

/// a field operation is either inserting a value into a field or its slice, or reading it
#[derive(Debug, PartialEq, Eq)]
pub enum FieldOps {
    InsertField(ArgExpr),
    InsertFieldSlices(Vec<FieldSliceOp>),
    ReadAction,
}

impl FieldOps {
    pub fn replace_symbolic_values(ops: Arc<FieldOps>, vals: &mut Vec<u64>) -> Arc<FieldOps> {
        match ops.as_ref() {
            FieldOps::InsertField(arg) => {
                Arc::new(FieldOps::InsertField(arg.replace_symbolic_values(vals)))
            }
            FieldOps::InsertFieldSlices(sliceops) => {
                let sliceops = sliceops
                    .iter()
                    .map(|a| a.replace_symbolic_values(vals))
                    .collect();
                Arc::new(FieldOps::InsertFieldSlices(sliceops))
            }
            FieldOps::ReadAction => ops,
        }
    }
}

/// a field ops is a list of operations on a given field,
#[derive(Debug, PartialEq)]
struct FieldOperations(Arc<String>, Arc<FieldOps>);

impl From<&FieldOperations> for Vec<Operation> {
    fn from(prog: &FieldOperations) -> Self {
        let mut ops = Vec::new();
        match prog.1.as_ref() {
            FieldOps::InsertField(arg) => {
                ops.push(Operation::Insert {
                    field: prog.0.to_string(),
                    slice: None,
                    arg: arg.into(),
                });
            }
            FieldOps::InsertFieldSlices(sliceops) => {
                for s in sliceops.iter() {
                    ops.push(Operation::Insert {
                        field: prog.0.to_string(),
                        slice: Some(s.0.to_string()),
                        arg: (&s.1).into(),
                    });
                }
            }
            FieldOps::ReadAction => {
                ops.push(Operation::ReadAction {
                    field: prog.0.to_string(),
                });
            }
        }
        ops.push(Operation::WriteAction {
            field: prog.0.to_string(),
        });
        ops
    }
}

/// the operations are a vector of field ops
#[derive(Clone, Debug)]
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

    pub fn get(&mut self) -> String {
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

impl Default for SymbolicVars {
    fn default() -> Self {
        Self::new()
    }
}

impl Program {
    pub fn new() -> Self {
        Self { ops: Vec::new() }
    }

    pub fn replace_symbolic_values(&mut self, vals: &mut Vec<u64>) {
        for op in self.ops.iter_mut() {
            *op = Arc::new(FieldOperations(
                op.0.clone(),
                FieldOps::replace_symbolic_values(op.1.clone(), vals),
            ));
        }
    }

    pub fn to_smt2(&self, fnname: &str, args: &[Param]) -> (Smt2Context, SymbolicVars) {
        let mut smt = Smt2Context::new();

        let mut smtops = Vec::new();

        let mut symvar = SymbolicVars::new();
        for fops in self.ops.iter() {
            match fops.1.deref() {
                FieldOps::InsertField(arg) => {
                    let arg = arg.to_term(&mut symvar);
                    let fname = format!("Model.IFace.{}.set!", fops.0);
                    smtops.push((fname, Some(arg)));
                }
                FieldOps::InsertFieldSlices(sliceops) => {
                    for sliceop in sliceops.iter() {
                        let arg = sliceop.1.to_term(&mut symvar);
                        let fname = format!("Model.IFace.{}.{}.set!", fops.0, sliceop.0);
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
                Some(a) => Term::fn_apply(f, vec![m, a]),
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

    pub fn merge(mut self, other: &Self) -> Self {
        let mut ops: HashMap<Arc<String>, Vec<Arc<FieldOps>>> = HashMap::new();

        // struct FieldOperations(Arc<String>, Arc<FieldOps>);
        for op in self.ops.iter() {
            if let Some(x) = ops.get_mut(&op.0) {
                x.push(op.1.clone());
            } else {
                ops.insert(op.0.clone(), vec![op.1.clone()]);
            }
        }

        for op in other.ops.iter() {
            if let Some(x) = ops.get_mut(&op.0) {
                x.push(op.1.clone());
            } else {
                ops.insert(op.0.clone(), vec![op.1.clone()]);
            }
        }

        let mut newops = Vec::new();
        let mut sliceops = Vec::new();
        for (fld, fops) in ops.iter_mut() {
            for fop in fops {
                match fop.as_ref() {
                    // FieldOps::InsertField(a) => {
                    //     if !sliceops.is_empty() {
                    //         let sops = FieldOps::InsertFieldSlices(sliceops.clone());
                    //         newops.push(FieldOperations(fld.clone(), Arc::new(sops)));
                    //         sliceops.clear();
                    //     }
                    //     newops.push(Arc::new(FieldOperations(fld.clone(), fop.clone())));
                    // }
                    FieldOps::InsertFieldSlices(slices) => {
                        sliceops.extend(slices.clone());
                    }
                    _ => {
                        if !sliceops.is_empty() {
                            let sops = FieldOps::InsertFieldSlices(sliceops.clone());
                            newops.push(Arc::new(FieldOperations(fld.clone(), Arc::new(sops))));
                            sliceops.clear();
                        }
                        if let Some(x) = newops.last() {
                            if x.0.as_ref() == fld.as_ref() && x.1.as_ref() == fop.as_ref() {
                                continue;
                            }
                        }
                        newops.push(Arc::new(FieldOperations(fld.clone(), fop.clone())));
                    }
                }
            }

            if !sliceops.is_empty() {
                let sops = FieldOps::InsertFieldSlices(sliceops.clone());
                newops.push(Arc::new(FieldOperations(fld.clone(), Arc::new(sops))));
            }
        }

        self.ops = newops;

        // for op in other.ops.iter() {
        //     if !self.ops.contains(&op) {
        //         self.ops.push(op.clone());
        //     }
        // }
        self
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Program> for Vec<Operation> {
    fn from(mut prog: Program) -> Self {
        let mut ops: Vec<Operation> = prog
            .ops
            .iter_mut()
            .flat_map(|o| {
                <&FieldOperations as std::convert::Into<Vec<Operation>>>::into(o.as_ref())
            })
            .collect();
        ops.push(Operation::Return);
        ops
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
        let slices = slices.into_iter().map(Arc::new).collect();
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
            let mut slice_programs: Vec<Vec<ArgExpr>> = slices.iter().map(|_| vec![]).collect();
            for slice in slices {
                // the new slice programs we've generated
                let mut new_slice_programs = Vec::new();

                // extend all programs by adding the variables
                for program in &slice_programs {
                    if !symbolic {
                        let mut program_new = program.clone();
                        program_new.push(ArgExpr::Arg(ArgX::One));
                        new_slice_programs.push(program_new);

                        let mut program_new = program.clone();
                        program_new.push(ArgExpr::Arg(ArgX::Zero));
                        new_slice_programs.push(program_new);

                        for var in &self.vars {
                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Arg(ArgX::Var(var.clone())));
                            new_slice_programs.push(program_new);
                        }
                    } else {
                        // add the constant number as well
                        let mut program_new = program.clone();
                        program_new.push(ArgExpr::Arg(ArgX::Num));
                        new_slice_programs.push(program_new);

                        for var in &self.vars {
                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Arg(ArgX::Var(var.clone())));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::RShift(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);
                        }
                    }
                }
                // set them as the current programs
                slice_programs = new_slice_programs;
            }

            // now we construct the programs to manipulate the fields
            let mut field_programs = Vec::new();
            field_programs.push(Arc::new(FieldOps::InsertField(ArgExpr::Arg(ArgX::Zero))));

            for mut program in slice_programs.drain(..) {
                let mut sliceops = Vec::new();
                for (_i, slice) in slices.iter().enumerate() {
                    sliceops.push(FieldSliceOp(slice.clone(), program.pop().unwrap()));
                }

                field_programs.push(Arc::new(FieldOps::InsertFieldSlices(sliceops)));
            }

            // add full field accesses as well
            // for var in &self.vars {
            //     field_programs.push(Arc::new(FieldOps::InsertField(ArgX::Var(var.clone()))));
            // }

            // now add the variants to modify the build to the field operations
            let ops = field_programs
                .into_iter()
                .map(|p| Arc::new(FieldOperations(field.clone(), p)))
                .collect();
            field_operations.push(ops);
        }

        // now build any possible compinatins of the programs

        let mut programs: Vec<Vec<Arc<FieldOperations>>> =
            self.fields.iter().map(|_| vec![]).collect();

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

impl Default for ProgramsBuilder {
    fn default() -> Self {
        Self::new()
    }
}
