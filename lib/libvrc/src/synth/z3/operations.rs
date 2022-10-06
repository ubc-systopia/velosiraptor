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

/// the arguments are for either a symbolic variable (num) or a variable (var), or a flag access
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
    /// represents a flag  var.flag
    Flag(Arc<String>, Arc<String>),
}

impl ArgX {
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        match self {
            ArgX::Num => {
                // the symvars have reverse order, so we can pop to get them in order.
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
            ArgX::Flag(v, f) => Term::fn_apply(
                format!("Flags.{}.get!", f),
                vec![Term::ident(format!("{}", v))],
            ),
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
            ArgX::Flag(v, f) => OpExpr::Flags(v.to_string(), f.to_string()),
        }
    }
}

/// the argment expressions can be some of a few operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgExpr {
    Arg(ArgX),
    RShift(ArgX, ArgX),
    Div(ArgX, ArgX),
    Mul(ArgX, ArgX),
    Add(ArgX, ArgX),
    Sub(ArgX, ArgX),
    And(ArgX, ArgX),
    Or(ArgX, ArgX),
    Not(ArgX),
    ShiftMask(ArgX, ArgX, ArgX),
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
            ArgExpr::And(a, b) => ArgExpr::And(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::Or(a, b) => ArgExpr::Or(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ArgExpr::ShiftMask(a, b, c) => ArgExpr::ShiftMask(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
                c.replace_symbolic_values(vals),
            ),
            ArgExpr::Not(a) => ArgExpr::Not(a.replace_symbolic_values(vals)),
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
            ArgExpr::And(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvand(x, y)
            }
            ArgExpr::Or(x, y) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                Term::bvor(x, y)
            }
            ArgExpr::ShiftMask(x, y, z) => {
                let x = x.to_term(symvar);
                let y = y.to_term(symvar);
                let z = z.to_term(symvar);
                Term::bvand(Term::bvshr(x, y), z)
            }
            ArgExpr::Not(x) => {
                let x = x.to_term(symvar);
                Term::bvnot(x)
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
            ArgExpr::And(x, y) => OpExpr::And(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ArgExpr::Or(x, y) => OpExpr::Or(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ArgExpr::ShiftMask(x, y, z) => OpExpr::And(
                Box::new(OpExpr::Shr(
                    Box::new(OpExpr::from(x)),
                    Box::new(OpExpr::from(y)),
                )),
                Box::new(OpExpr::from(z)),
            ),
            ArgExpr::Not(x) => OpExpr::Not(Box::new(OpExpr::from(x))),
        }
    }
}

/// the filed slice operation sets a value of a field slice
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FieldSliceOp(Arc<String>, ArgExpr);

impl FieldSliceOp {
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> FieldSliceOp {
        FieldSliceOp(self.0.clone(), self.1.replace_symbolic_values(vals))
    }
}

/// a field operation is either inserting a value into a field or its slice, or reading it
#[derive(Debug, PartialEq, Eq)]
pub enum FieldOp {
    InsertField(ArgExpr),
    InsertFieldSlices(Vec<FieldSliceOp>),
    ReadAction,
    WriteAction,
}

impl FieldOp {
    pub fn replace_symbolic_values(ops: Arc<FieldOp>, vals: &mut Vec<u64>) -> Arc<FieldOp> {
        match ops.as_ref() {
            FieldOp::InsertField(arg) => {
                Arc::new(FieldOp::InsertField(arg.replace_symbolic_values(vals)))
            }
            FieldOp::InsertFieldSlices(sliceops) => {
                let sliceops = sliceops
                    .iter()
                    .map(|a| a.replace_symbolic_values(vals))
                    .collect();
                Arc::new(FieldOp::InsertFieldSlices(sliceops))
            }
            FieldOp::ReadAction => ops,
            FieldOp::WriteAction => ops,
        }
    }
}

/// a field ops is a list of operations on a given field,
#[derive(Debug, PartialEq, Eq, Clone)]
struct FieldOperations(Arc<String>, Vec<Arc<FieldOp>>);

impl From<&FieldOperations> for Vec<Operation> {
    fn from(prog: &FieldOperations) -> Self {
        let mut ops = Vec::new();
        for op in &prog.1 {
            match op.as_ref() {
                FieldOp::InsertField(arg) => {
                    ops.push(Operation::Insert {
                        field: prog.0.to_string(),
                        slice: None,
                        arg: arg.into(),
                    });
                }
                FieldOp::InsertFieldSlices(sliceops) => {
                    for s in sliceops.iter() {
                        ops.push(Operation::Insert {
                            field: prog.0.to_string(),
                            slice: Some(s.0.to_string()),
                            arg: (&s.1).into(),
                        });
                    }
                }
                FieldOp::ReadAction => {
                    ops.push(Operation::ReadAction {
                        field: prog.0.to_string(),
                    });
                }
                FieldOp::WriteAction => {
                    ops.push(Operation::WriteAction {
                        field: prog.0.to_string(),
                    });
                }
            }
        }
        // and add the write action
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
                op.1.iter()
                    .map(|a| FieldOp::replace_symbolic_values(a.clone(), vals))
                    .collect(),
            ));
        }
    }

    pub fn to_smt2(&self, fnname: &str, args: &[Param]) -> (Smt2Context, SymbolicVars) {
        let mut smt = Smt2Context::new();

        let mut smtops = Vec::new();

        let mut symvar = SymbolicVars::new();
        for fops in self.ops.iter() {
            for op in &fops.1 {
                match op.deref() {
                    FieldOp::InsertField(arg) => {
                        let arg = arg.to_term(&mut symvar);
                        let fname = format!("Model.IFace.{}.set!", fops.0);
                        smtops.push((fname, Some(arg)));
                    }
                    FieldOp::InsertFieldSlices(sliceops) => {
                        for sliceop in sliceops.iter() {
                            let arg = sliceop.1.to_term(&mut symvar);
                            let fname = format!("Model.IFace.{}.{}.set!", fops.0, sliceop.0);
                            smtops.push((fname, Some(arg)));
                        }
                    }
                    FieldOp::ReadAction => {
                        let fname = format!("Model.IFace.{}.readaction ", fops.0);
                        smtops.push((fname, None));
                    }
                    FieldOp::WriteAction => {
                        let fname = format!("Model.IFace.{}.writeaction ", fops.0);
                        smtops.push((fname, None));
                    }
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
        let mut ops: HashMap<Arc<String>, Vec<Arc<FieldOp>>> = HashMap::new();

        // struct FieldOperations(Arc<String>, Vec<Arc<FieldOp>>);
        for op in self.ops.iter() {
            if let Some(x) = ops.get_mut(&op.0) {
                x.extend(op.1.clone());
            } else {
                ops.insert(op.0.clone(), op.1.clone());
            }
        }

        for op in other.ops.iter() {
            if let Some(x) = ops.get_mut(&op.0) {
                for o in op.1.iter() {
                    if !x.contains(o) {
                        x.push(o.clone());
                    }
                }
            //    x.push(op.1.clone());
            } else {
                ops.insert(op.0.clone(), op.1.clone());
            }
        }

        let mut newops = Vec::new();

        for (fld, fops) in ops.iter_mut() {
            let mut fieldops: Vec<Arc<FieldOp>> = Vec::new();
            let mut sliceops = Vec::new();
            for fop in fops {
                match fop.as_ref() {
                    // FieldOp::InsertField(a) => {
                    //     if !sliceops.is_empty() {
                    //         let sops = FieldOp::InsertFieldSlices(sliceops.clone());
                    //         newops.push(FieldOperations(fld.clone(), Arc::new(sops)));
                    //         sliceops.clear();
                    //     }
                    //     newops.push(Arc::new(FieldOperations(fld.clone(), fop.clone())));
                    // }
                    FieldOp::InsertFieldSlices(slices) => {
                        sliceops.extend(slices.clone());
                    }

                    _ => {
                        if !sliceops.is_empty() {
                            let sops = Arc::new(FieldOp::InsertFieldSlices(sliceops.clone()));
                            fieldops.push(sops);
                            sliceops.clear();
                        } else {
                            if fieldops.contains(fop) {
                                continue;
                            }
                            fieldops.push(fop.clone());
                        }

                        // if let Some(x) = fieldops.last() {
                        //     if x.as_ref() == fld.as_ref() && x.1.contains(fop) {
                        //         continue;
                        //     }
                        // } else {

                        // }
                        // newops.push(Arc::new(FieldOperations(fld.clone(), vec![fop.clone()])));
                    }
                }
            }

            if !sliceops.is_empty() {
                let sops = Arc::new(FieldOp::InsertFieldSlices(sliceops));
                fieldops.push(sops);
            }

            newops.push(Arc::new(FieldOperations(fld.clone(), fieldops)));
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

    pub fn construct_programs(&self, symbolic: bool) -> Vec<Program> {
        // a vector with an entry for each field that contains a vector for
        // all possible operations on this field
        let mut field_operations: Vec<Vec<Arc<FieldOperations>>> = Vec::new();
        let mut field_operations_2: Vec<Vec<Arc<FieldOperations>>> = Vec::new();

        // TODO: Revisit this!

        // now we loop over each field and slices to construct all possible operations
        for (field, slices) in &self.fields {
            // all programs that operate on the slices of this field
            let mut slice_programs: Vec<Vec<ArgExpr>> = slices.iter().map(|_| vec![]).collect();
            for _slice in slices {
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

                        for (v, f) in &self.flags {
                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Arg(ArgX::Flag(v.clone(), f.clone())));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Not(ArgX::Flag(v.clone(), f.clone())));
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

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::ShiftMask(
                                ArgX::Var(var.clone()),
                                ArgX::Num,
                                ArgX::Num,
                            ));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Add(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Sub(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Mul(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);

                            // let mut program_new = program.clone();
                            // program_new.push(ArgExpr::Div(ArgX::Var(var.clone()), ArgX::Num));
                            // new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::And(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Or(ArgX::Var(var.clone()), ArgX::Num));
                            new_slice_programs.push(program_new);
                        }

                        for (v, f) in &self.flags {
                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Arg(ArgX::Flag(v.clone(), f.clone())));
                            new_slice_programs.push(program_new);

                            let mut program_new = program.clone();
                            program_new.push(ArgExpr::Not(ArgX::Flag(v.clone(), f.clone())));
                            new_slice_programs.push(program_new);
                        }
                    }
                }
                // set them as the current programs
                slice_programs = new_slice_programs;
            }

            // now we construct the programs to manipulate the fields
            let mut field_programs = Vec::new();
            //field_programs.push(Arc::new(FieldOp::ReadAction));
            field_programs.push(Arc::new(FieldOp::InsertField(ArgExpr::Arg(ArgX::Zero))));

            for mut program in slice_programs.drain(..) {
                let mut sliceops = Vec::new();
                for (_i, slice) in slices.iter().enumerate() {
                    sliceops.push(FieldSliceOp(slice.clone(), program.pop().unwrap()));
                }

                field_programs.push(Arc::new(FieldOp::InsertFieldSlices(sliceops)));
            }

            // add full field accesses as well
            // for var in &self.vars {
            //     field_programs.push(Arc::new(FieldOp::InsertField(ArgX::Var(var.clone()))));
            // }

            // now add the variants to modify the build to the field operations
            let ops = field_programs
                .iter()
                .map(|p| Arc::new(FieldOperations(field.clone(), vec![p.clone()])))
                .collect();

            field_operations.push(ops);

            let ops = field_programs
                .into_iter()
                .map(|p| {
                    Arc::new(FieldOperations(
                        field.clone(),
                        vec![Arc::new(FieldOp::ReadAction), p],
                    ))
                })
                .collect();

            field_operations_2.push(ops);
        }

        // now build any possible compinatins of the programs

        let mut final_programs = Vec::new();

        // we need to do something for each program

        let mut programs: Vec<Vec<Arc<FieldOperations>>> =
            self.fields.iter().map(|_| vec![]).collect();

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

        final_programs.extend(programs);

        let mut programs: Vec<Vec<Arc<FieldOperations>>> =
            self.fields.iter().map(|_| vec![]).collect();

        for fops in field_operations_2 {
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

        final_programs.extend(programs);

        // and conver the programs into the final format
        final_programs
            .into_iter()
            .map(|p| Program { ops: p })
            .collect()
    }
}

impl Default for ProgramsBuilder {
    fn default() -> Self {
        Self::new()
    }
}
