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

use smt2::{Function, Smt2Context, Term, VarBinding};

use velosiast::ast::VelosiAstParam;

use crate::model;
use crate::{OpExpr, Operation};

mod builder;
mod statevars;
mod symvars;

use statevars::StateVars;

// public re-exports
pub use builder::ProgramsBuilder;
pub use symvars::SymbolicVars;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Literals
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Literals -- Integers, Symbolic variables, and Flags
///
/// Literals form the terminals of the grammar for constructing programs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    /// a constant, arbitrary 64-bit number, common used values are 0 and 1
    Val(u64),
    /// a symbolic constant number   TODO: add an identifier here
    Num,
    /// a variable
    Var(Arc<String>),
    /// represents a flag  var.flag
    Flag(Arc<String>, Arc<String>),
}

impl Literal {
    /// Rewrites the [Literal] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        match self {
            Literal::Num => {
                // the symvars have reverse order, so we can pop to get them in order.
                let val = vals.pop().unwrap();
                Literal::Val(val)
            }
            s => s.clone(),
        }
    }

    /// Converts the [Literal] into a [Term] for smt query
    pub fn to_smt2_term(&self, symvars: &mut SymbolicVars) -> Term {
        match self {
            Literal::Num => Term::ident(symvars.get()),
            Literal::Var(v) => Term::ident(v.to_string()),
            Literal::Val(v) => Term::num(*v),
            Literal::Flag(v, f) => Term::fn_apply(
                format!("Flags.{}.get!", f),
                vec![Term::ident(v.to_string())],
            ),
        }
    }
}

/// Conversion of [Literal] to [OpExpr] for the programs we use
impl From<&Literal> for OpExpr {
    fn from(prog: &Literal) -> Self {
        match prog {
            Literal::Val(val) => OpExpr::Num(*val),
            Literal::Num => {
                // when converting to the OpExpr all symbolic variables should have been
                // replaced with the corresponding concrete value
                unreachable!("symbolic values not replaced!")
            }
            Literal::Var(v) => OpExpr::Var(v.to_string()),
            Literal::Flag(v, f) => OpExpr::Flags(v.to_string(), f.to_string()),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Expressions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Expressions over Literals
///
/// Expressions are used to compute values for the interface operations. They support a basic
/// arithmetic operations, bitwise operations and a shift/mask operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    /// the literal without any operation
    Lit(Literal),
    /// logic right shift: `a >> b`
    RShift(Literal, Literal),
    /// left shift operation: `a << b`
    LShift(Literal, Literal),
    /// division operation: `a / b`
    Div(Literal, Literal),
    /// multiplication operation: `a * b`
    Mul(Literal, Literal),
    /// addition operation: `a + b`
    Add(Literal, Literal),
    /// subtraction operation: `a - b`
    Sub(Literal, Literal),
    /// bitwise and operation:  `a & b`
    And(Literal, Literal),
    /// bitwise or operation: `a | b`
    Or(Literal, Literal),
    /// bitwise not operation: `!a`
    Not(Literal),
    /// sift and mask operation: `(a >> b) & c`
    ShiftMask(Literal, Literal, Literal),
}

impl Expression {
    /// Rewrites the [Expression] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        use Expression::*;
        match self {
            Lit(x) => Lit(x.replace_symbolic_values(vals)),
            RShift(a, b) => RShift(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            LShift(a, b) => LShift(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            Div(a, b) => Div(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            Mul(a, b) => Mul(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            Add(a, b) => Add(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            Sub(a, b) => Sub(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            And(a, b) => And(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            Or(a, b) => Or(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
            ),
            ShiftMask(a, b, c) => ShiftMask(
                a.replace_symbolic_values(vals),
                b.replace_symbolic_values(vals),
                c.replace_symbolic_values(vals),
            ),
            Not(a) => Not(a.replace_symbolic_values(vals)),
        }
    }

    /// Converts the [Expression] into a [Term] for smt query
    pub fn to_smt2_term(&self, symvars: &mut SymbolicVars) -> Term {
        use Expression::*;
        match self {
            Lit(x) => x.to_smt2_term(symvars),
            RShift(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvshr(x, y)
            }
            LShift(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvshl(x, y)
            }
            Div(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvdiv(x, y)
            }
            Mul(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvmul(x, y)
            }
            Add(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvadd(x, y)
            }
            Sub(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvsub(x, y)
            }
            And(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvand(x, y)
            }
            Or(x, y) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                Term::bvor(x, y)
            }
            ShiftMask(x, y, z) => {
                let x = x.to_smt2_term(symvars);
                let y = y.to_smt2_term(symvars);
                let z = z.to_smt2_term(symvars);
                Term::bvand(Term::bvshr(x, y), z)
            }
            Not(x) => {
                let x = x.to_smt2_term(symvars);
                Term::bvnot(x)
            }
        }
    }
}

impl From<&Expression> for OpExpr {
    fn from(prog: &Expression) -> Self {
        use Expression::*;
        match prog {
            Lit(x) => OpExpr::from(x),
            RShift(x, y) => OpExpr::Shr(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            LShift(x, y) => OpExpr::Shl(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            Div(x, y) => OpExpr::Div(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            Mul(x, y) => OpExpr::Mul(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            Add(x, y) => OpExpr::Add(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            Sub(x, y) => OpExpr::Sub(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            And(x, y) => OpExpr::And(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            Or(x, y) => OpExpr::Or(Box::new(OpExpr::from(x)), Box::new(OpExpr::from(y))),
            ShiftMask(x, y, z) => OpExpr::And(
                Box::new(OpExpr::Shr(
                    Box::new(OpExpr::from(x)),
                    Box::new(OpExpr::from(y)),
                )),
                Box::new(OpExpr::from(z)),
            ),
            Not(x) => OpExpr::Not(Box::new(OpExpr::from(x))),
        }
    }
}

impl From<Arc<Expression>> for OpExpr {
    fn from(prog: Arc<Expression>) -> Self {
        OpExpr::from(prog.as_ref())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Slice Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Slice Operations -- Inserting  Bits in Field Slices
///
/// A field slice operation represents the expression to be inserted into a specific field slice
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldSliceOp(Arc<String>, Arc<Expression>);

impl FieldSliceOp {
    /// Rewrites the [FieldSliceOp] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&mut self, vals: &mut Vec<u64>) {
        self.1 = Arc::new(self.1.replace_symbolic_values(vals));
    }

    /// Converts the [Expression] into a [Term] for smt query
    pub fn to_smt2_term(
        &self,
        smtops: &mut Vec<(String, Option<Term>)>,
        symvars: &mut SymbolicVars,
    ) {
        let arg = self.1.to_smt2_term(symvars);
        let fname = format!("Model.IFace.{}.set!", self.0);
        smtops.push((fname, Some(arg)));
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Operation -- Reading/Writing Interface Fields, constructing the value thereof.
///
/// A field operation either inserts value into the full field, constructs a value from a sequence
/// of field slices, or reads/writes the field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldOp {
    /// set the field value to be expression
    InsertField(Arc<Expression>),
    /// insert values into particular slices of the field
    InsertFieldSlices(Vec<FieldSliceOp>),
    /// performs the read action on the field
    ReadAction,
    /// performs the write action on the field
    WriteAction,
}

impl FieldOp {
    /// Rewrites the [FieldSliceOp] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&mut self, vals: &mut Vec<u64>) {
        use FieldOp::*;
        match self {
            InsertField(arg) => *arg = Arc::new(arg.replace_symbolic_values(vals)),
            InsertFieldSlices(sliceops) => sliceops
                .iter_mut()
                .for_each(|a| a.replace_symbolic_values(vals)),
            _ => (),
        }
    }

    /// Converts the [Expression] into a [Term] for smt query
    pub fn to_smt2_term(
        &self,
        fieldname: &str,
        smtops: &mut Vec<(String, Option<Term>)>,
        symvars: &mut SymbolicVars,
    ) {
        match self {
            FieldOp::InsertField(arg) => {
                let arg = arg.to_smt2_term(symvars);
                let fname = format!("Model.IFace.{}.set!", fieldname);
                smtops.push((fname, Some(arg)));
            }
            FieldOp::InsertFieldSlices(sliceops) => {
                sliceops
                    .iter()
                    .for_each(|f| f.to_smt2_term(smtops, symvars));
            }
            FieldOp::ReadAction => {
                let fname = format!("Model.IFace.{}.readaction ", fieldname);
                smtops.push((fname, None));
            }
            FieldOp::WriteAction => {
                let fname = format!("Model.IFace.{}.writeaction ", fieldname);
                smtops.push((fname, None));
            }
        }
    }

    /// Checks whether the `other` would overwrite the effect of `self`
    pub fn would_overwrite(&self, other: &Self) -> bool {
        use FieldOp::*;
        match (self, other) {
            (InsertField(_), InsertField(_)) => true,
            (InsertFieldSlices(_), InsertField(_)) => true,
            (InsertFieldSlices(a), InsertFieldSlices(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                // if all slice elements are the same
                a.iter().zip(b.iter()).all(|(a, b)| a.0 == b.0)
            }
            _ => false,
        }
    }

    pub fn to_operations(&self, fieldname: &str) -> Vec<Operation> {
        use FieldOp::*;
        match self {
            InsertField(arg) => {
                vec![Operation::Insert {
                    field: fieldname.to_string(),
                    slice: None,
                    arg: arg.as_ref().into(),
                }]
            }
            InsertFieldSlices(sliceops) => sliceops
                .iter()
                .map(|s| Operation::Insert {
                    field: fieldname.to_string(),
                    slice: Some(s.0.to_string()),
                    arg: s.1.as_ref().into(),
                })
                .collect(),
            ReadAction => {
                vec![Operation::ReadAction {
                    field: fieldname.to_string(),
                }]
            }
            WriteAction => {
                vec![Operation::WriteAction {
                    field: fieldname.to_string(),
                }]
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Actions -- A sequence of field operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Actions -- A sequence of field operations on a field
#[derive(Debug, PartialEq, Eq, Clone)]
struct FieldActions(Arc<String>, Vec<FieldOp>);

impl FieldActions {
    /// Rewrites the [FieldActions] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&self, vals: &mut Vec<u64>) -> Self {
        Self(
            self.0.clone(),
            self.1
                .iter()
                .map(|a| {
                    let mut a = a.clone();
                    a.replace_symbolic_values(vals);
                    a
                })
                .collect(),
        )
    }

    /// Converts the [Expression] into a [Term] for smt query
    pub fn to_smt2_term(
        &self,
        smtops: &mut Vec<(String, Option<Term>)>,
        symvars: &mut SymbolicVars,
    ) {
        self.1
            .iter()
            .for_each(|f| f.to_smt2_term(self.0.as_str(), smtops, symvars));

        // field actions always end with a write action
        let fname = format!("Model.IFace.{}.writeaction ", self.0);
        smtops.push((fname, None));
    }
}

impl From<&FieldActions> for Vec<Operation> {
    fn from(prog: &FieldActions) -> Self {
        let mut ops = Vec::new();
        for op in &prog.1 {
            ops.extend(op.to_operations(prog.0.as_str()));
        }
        // and add the write action
        ops.push(Operation::WriteAction {
            field: prog.0.to_string(),
        });
        ops
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Program -- A full configuration sequence
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Program -- A sequence of field operations
///
/// A program represents the sequence of operations on fields that perform the configuration
/// sequence.
#[derive(Clone, Debug)]
pub struct Program(Vec<Arc<FieldActions>>);

impl Program {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Rewrites the [FieldActions] by replacing symbolic variables with their concrete values
    ///
    /// This requires that the symbolic variables appear in revers order in that they were
    /// introduced.
    pub fn replace_symbolic_values(&mut self, vals: &mut Vec<u64>) {
        self.0
            .iter_mut()
            .for_each(|a| *a = Arc::new(a.replace_symbolic_values(vals)));
    }

    /// Converts the [Expression] into a [Smt2Context] for smt query
    ///
    /// Creates the SMT contxt with the symbolic variable definitions and the
    /// function to do the state transitions in the model.
    pub fn to_smt2_term(
        &self,
        fnname: &str,
        args: &[VelosiAstParam],
    ) -> (Smt2Context, SymbolicVars) {
        // new symbolic variables
        let mut symvar = SymbolicVars::new();

        // get the secquence of smt2 operations as a (fn, args) pair.
        let mut smtops = Vec::new();
        self.0
            .iter()
            .for_each(|f| f.to_smt2_term(&mut smtops, &mut symvar));

        // the state variable of the current state
        let mut stvar = StateVars::new();

        // add the function definition of the program
        //
        // This creates a function in the form:
        // fn map(args) :
        //   let st1 = op1(st)
        //   let st2 = op2(st1)
        //   st2
        let mut f = Function::new(fnname.to_string(), String::from("Model_t"));
        f.add_arg(stvar.current(), model::types::model());
        for arg in args.iter() {
            f.add_arg(
                arg.ident_to_string(),
                model::types::type_to_smt2(&arg.ptype),
            );
        }

        // the smt definitinos
        let mut defs = Vec::new();
        for (_i, (f, a)) in smtops.drain(..).enumerate() {
            // the model var term for smt2
            let m = Term::ident(stvar.current());

            // construct the function application term with the supplied argument and the name of
            // the function
            let fcall = match a {
                Some(a) => Term::fn_apply(f, vec![m, a]),
                None => Term::fn_apply(f, vec![m]),
            };

            defs.push(VarBinding::new(stvar.next(), fcall));
        }

        // construct the body as a sequence of let expressions
        let body = defs
            .into_iter()
            .rev()
            .fold(Term::ident(stvar.current()), |acc, x| {
                Term::letexpr(vec![x], acc)
            });

        // set the function body and add it to the smt2 context.
        f.add_body(body);

        // create a new Smt2Context with the symbolic variables and the function
        let mut smt = Smt2Context::new();
        symvar.add_to_context(&mut smt);
        smt.function(f);

        (smt, symvar)
    }

    /// Merges two programs together
    ///
    /// This combines two programs by merging the respective field actions together
    pub fn merge(mut self, other: &Self) -> Self {
        let mut ops: HashMap<Arc<String>, Vec<FieldOp>> = HashMap::new();

        // struct FieldActions(Arc<String>, Vec<Arc<FieldOp>>);
        for op in self.0.iter() {
            if let Some(x) = ops.get_mut(&op.0) {
                x.extend(op.1.clone());
            } else {
                ops.insert(op.0.clone(), op.1.clone());
            }
        }

        for op in other.0.iter() {
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
            let mut fieldops: Vec<FieldOp> = Vec::new();
            let mut sliceops = Vec::new();
            for fop in fops {
                match fop {
                    // FieldOp::InsertField(a) => {
                    //     if !sliceops.is_empty() {
                    //         let sops = FieldOp::InsertFieldSlices(sliceops.clone());
                    //         newops.push(FieldActions(fld.clone(), Arc::new(sops)));
                    //         sliceops.clear();
                    //     }
                    //     newops.push(Arc::new(FieldActions(fld.clone(), fop.clone())));
                    // }
                    FieldOp::InsertFieldSlices(slices) => {
                        sliceops.extend(slices.clone());
                    }

                    _ => {
                        if !sliceops.is_empty() {
                            let sops = FieldOp::InsertFieldSlices(sliceops.clone());
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
                        // newops.push(Arc::new(FieldActions(fld.clone(), vec![fop.clone()])));
                    }
                }
            }

            if !sliceops.is_empty() {
                let sops = FieldOp::InsertFieldSlices(sliceops);
                fieldops.push(sops);
            }

            newops.push(Arc::new(FieldActions(fld.clone(), fieldops)));
        }

        self.0 = newops;

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
            .0
            .iter_mut()
            .flat_map(|o| <&FieldActions as std::convert::Into<Vec<Operation>>>::into(o))
            .collect();
        ops.push(Operation::Return);
        ops
    }
}
