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
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;
use std::sync::Arc;

use smt2::{Function, Smt2Context, Term, VarBinding};

use velosiast::ast::{VelosiAstParam, VelosiOpExpr, VelosiOperation};

use crate::model;
use crate::model::velosimodel::{IFACE_PREFIX, LOCAL_VARS_PREFIX, MODEL_PREFIX, WBUFFER_PREFIX};

mod builder;
mod statevars;
mod symvars;

use statevars::StateVars;

// public re-exports
pub use builder::{MultiDimIterator, ProgramsBuilder, ProgramsIter};
pub use symvars::SymbolicVars;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Literals
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Literals -- Integers, Symbolic variables, and Flags
///
/// Literals form the terminals of the grammar for constructing programs.
#[derive(Clone, PartialEq, Eq, Hash)]
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

impl std::fmt::Debug for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Val(arg0) => write!(f, "Val(0x{arg0:x?})"),
            Self::Num => write!(f, "Num"),
            Self::Var(arg0) => f.debug_tuple("Var").field(arg0).finish(),
            Self::Flag(arg0, arg1) => f.debug_tuple("Flag").field(arg0).field(arg1).finish(),
        }
    }
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
            Literal::Flag(v, f) => {
                Term::fn_apply(format!("Flags.{f}.get!"), vec![Term::ident(v.to_string())])
            }
        }
    }
}

/// Conversion of [Literal] to [VelosiOpExpr] for the programs we use
impl From<&Literal> for VelosiOpExpr {
    fn from(prog: &Literal) -> Self {
        match prog {
            Literal::Val(val) => VelosiOpExpr::Num(*val),
            Literal::Num => {
                // when converting to the OpExpr all symbolic variables should have been
                // replaced with the corresponding concrete value
                unreachable!("symbolic values not replaced!")
            }
            Literal::Var(v) => VelosiOpExpr::Var(v.to_string()),
            Literal::Flag(v, f) => VelosiOpExpr::Flags(v.to_string(), f.to_string()),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Literal::Val(v) => write!(f, "0x{:x}", v),
            Literal::Num => write!(f, "?"),
            Literal::Var(v) => write!(f, "{}", v),
            Literal::Flag(v, fl) => write!(f, "{}.{}", v, fl),
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    /// the literal without any operation
    Lit(Literal),
    /// logic right shift: `a >> b`
    // RShift(Literal, Literal),  // replace the right shift with the ShiftMask
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
            // RShift(a, b) => RShift(
            //     a.replace_symbolic_values(vals),
            //     b.replace_symbolic_values(vals),
            // ),
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

    pub fn skip_for_bits(&self, bits: usize) -> bool {
        use Expression::*;
        match (bits, self) {
            // all with 0 bits
            (0, _) => true,
            // with 1 bits, we can basicaly remove a lot of operations...
            (1, Lit(Literal::Val(_))) => false,
            (1, Lit(Literal::Num)) => false, // skip arbitrary numbers
            (1, Lit(Literal::Var(_))) => true, // we skip the base variable
            (1, Lit(Literal::Flag(_, _))) => false,
            // (1, RShift(_, _)) => true, // keep right shifts
            (1, LShift(_, _)) => true, // left shifts are useless here...
            (1, Div(_, _)) => true,
            (1, Mul(_, _)) => true,
            (1, Add(_, _)) => true,
            (1, Sub(_, _)) => true,
            (1, And(_, Literal::Val(1))) => false,
            (1, And(_, Literal::Flag(_, _))) => false,
            (1, And(_, _)) => true,
            (1, Or(_, Literal::Flag(_, _))) => false,
            (1, Or(_, _)) => true, // skip Or,
            (1, ShiftMask(_, _, Literal::Val(1))) => false,
            (1, ShiftMask(_, _, _)) => true,
            (1, Not(_)) => false, // don't skip negations
            _ => false,
        }
    }

    /// Converts the [Expression] into a [Term] for smt query
    pub fn to_smt2_term(&self, symvars: &mut SymbolicVars) -> Term {
        use Expression::*;
        match self {
            Lit(x) => x.to_smt2_term(symvars),
            // RShift(x, y) => {
            //     let x = x.to_smt2_term(symvars);
            //     let y = y.to_smt2_term(symvars);
            //     Term::bvshr(x, y)
            // }
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

impl From<&Expression> for VelosiOpExpr {
    fn from(prog: &Expression) -> Self {
        use Expression::*;
        match prog {
            Lit(x) => VelosiOpExpr::from(x),
            //RShift(x, y) => VelosiOpExpr::Shr(Box::new(VelosiOpExpr::from(x)), Box::new(VelosiOpExpr::from(y))),
            LShift(x, y) => VelosiOpExpr::Shl(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            Div(x, y) => VelosiOpExpr::Div(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            Mul(x, y) => VelosiOpExpr::Mul(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            Add(x, y) => VelosiOpExpr::Add(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            Sub(x, y) => VelosiOpExpr::Sub(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            And(x, y) => VelosiOpExpr::And(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            Or(x, y) => VelosiOpExpr::Or(
                Box::new(VelosiOpExpr::from(x)),
                Box::new(VelosiOpExpr::from(y)),
            ),
            ShiftMask(x, y, z) => VelosiOpExpr::And(
                Box::new(VelosiOpExpr::Shr(
                    Box::new(VelosiOpExpr::from(x)),
                    Box::new(VelosiOpExpr::from(y)),
                )),
                Box::new(VelosiOpExpr::from(z)),
            ),
            Not(x) => VelosiOpExpr::Not(Box::new(VelosiOpExpr::from(x))),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Expression::*;
        match self {
            Lit(l) => Display::fmt(&l, f),
            LShift(x, y) => write!(f, "{} << {}", x, y),
            Div(x, y) => write!(f, "{} / {}", x, y),
            Mul(x, y) => write!(f, "{} * {}", x, y),
            Add(x, y) => write!(f, "{} + {}", x, y),
            Sub(x, y) => write!(f, "{} - {}", x, y),
            And(x, y) => write!(f, "{} & {}", x, y),
            Or(x, y) => write!(f, "{} | {}", x, y),
            Not(x) => write!(f, "!{}", x),
            ShiftMask(x, y, z) => write!(f, "({} >> {}) & {}", x, y, z),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Slice Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Slice Operations -- Inserting  Bits in Field Slices
///
/// A field slice operation represents the expression to be inserted into a specific field slice
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        fieldname: &str,
        smtops: &mut Vec<(String, Option<Term>)>,
        symvars: &mut SymbolicVars,
    ) {
        let arg = self.1.to_smt2_term(symvars);
        let fname = format!(
            "{MODEL_PREFIX}.{LOCAL_VARS_PREFIX}.{}.{}.set!",
            fieldname, self.0
        );
        smtops.push((fname, Some(arg)));
    }
}

impl Display for FieldSliceOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, ".set_{}({})", self.0, self.1)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Operation -- Reading/Writing Interface Fields, constructing the value thereof.
///
/// A field operation either inserts value into the full field, constructs a value from a sequence
/// of field slices, or reads/writes the field.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldOp {
    /// set the field value to be expression
    InsertField(Arc<Expression>),
    /// insert values into particular slices of the field
    InsertFieldSlices(Vec<FieldSliceOp>),
    /// performs the read action on the field
    ReadAction,
    // /// performs the write action on the field
    // WriteAction,
}

impl Display for FieldOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            FieldOp::InsertField(e) => {
                write!(f, ".set({}).write()", e)
            }
            FieldOp::InsertFieldSlices(ops) => {
                for op in ops {
                    Display::fmt(&op, f)?;
                }
                write!(f, ".write()")
            }
            FieldOp::ReadAction => write!(f, ".read()"),
        }
    }
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
                let fname = format!("{MODEL_PREFIX}.{LOCAL_VARS_PREFIX}.{fieldname}.set!");
                smtops.push((fname, Some(arg)));
            }
            FieldOp::InsertFieldSlices(sliceops) => {
                sliceops
                    .iter()
                    .for_each(|f| f.to_smt2_term(fieldname, smtops, symvars));
            }
            FieldOp::ReadAction => {
                let fname = format!("{MODEL_PREFIX}.{IFACE_PREFIX}.{fieldname}.readaction! ");
                smtops.push((fname, None));
            } // FieldOp::WriteAction => {
              //     let fname = format!("{MODEL_PREFIX}.IFace.{}.writeaction! ", fieldname);
              //     smtops.push((fname, None));
              // }
        }
    }

    pub fn merge_field_slices(&mut self, other: Self) {
        use FieldOp::*;

        if let (InsertFieldSlices(ex_ops), InsertFieldSlices(b)) = (self, other) {
            for new_op in b.into_iter() {
                // if there is any existing operation on the same slice, continue
                if ex_ops.iter().any(|a| a.0 == new_op.0) {
                    continue;
                }
                // add the new operation to the
                ex_ops.push(new_op);
            }
        }
    }

    pub fn to_operations(&self, fieldname: Rc<String>) -> Vec<VelosiOperation> {
        use FieldOp::*;
        match self {
            InsertField(arg) => {
                vec![VelosiOperation::InsertField(fieldname, arg.as_ref().into())]
            }
            InsertFieldSlices(sliceops) => sliceops
                .iter()
                .map(|s| {
                    VelosiOperation::InsertSlice(
                        fieldname.clone(),
                        Rc::new(s.0.to_string()),
                        s.1.as_ref().into(),
                    )
                })
                .collect(),
            ReadAction => {
                vec![VelosiOperation::ReadAction(fieldname)]
            } // WriteAction => {
              //     vec![Operation::WriteAction {
              //         field: fieldname.to_string(),
              //     }]
              // }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Field Actions -- A sequence of field operations
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Field Actions -- A sequence of field operations on a field
#[derive(PartialEq, Eq, Clone, Hash)]
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
        let fname = format!("{MODEL_PREFIX}.{LOCAL_VARS_PREFIX}.{}.storeaction!", self.0);
        smtops.push((fname, None));
        // TODO: only flush once at end
        let fname = format!("{MODEL_PREFIX}.{WBUFFER_PREFIX}.flushaction!");
        smtops.push((fname, None));
        // TODO: combine into flush action
        let fname = format!("{MODEL_PREFIX}.{IFACE_PREFIX}.{}.writeaction! ", self.0);
        smtops.push((fname, None));
    }
}

impl From<&FieldActions> for Vec<VelosiOperation> {
    fn from(prog: &FieldActions) -> Self {
        let mut ops = Vec::new();
        for op in &prog.1 {
            ops.extend(op.to_operations(Rc::new(prog.0.to_string())));
        }
        // and add the write action
        ops.push(VelosiOperation::WriteAction(Rc::new(prog.0.to_string())));
        ops
    }
}

impl Display for FieldActions {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let mut newline = true;
        for a in self.1.iter() {
            if newline {
                write!(f, "\n  {}", self.0)?;
                newline = false;
            }
            match a {
                FieldOp::InsertField(e) => {
                    if !newline {
                        write!(f, "\n    ")?;
                    }
                    write!(f, ".set({})", e)?;
                    if !newline {
                        write!(f, "\n    ")?;
                    }
                    write!(f, ".write()")?;
                    newline = true;
                }
                FieldOp::InsertFieldSlices(ops) => {
                    for op in ops {
                        if !newline {
                            write!(f, "\n    ")?;
                        }
                        Display::fmt(&op, f)?;
                    }
                    if !newline {
                        write!(f, "\n    ")?;
                    }
                    write!(f, ".write()")?;
                    newline = true;
                }
                FieldOp::ReadAction => write!(f, ".read()")?,
            }
        }
        Ok(())
    }
}

impl Debug for FieldActions {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for a in self.1.iter() {
            write!(f, "{}.{:?}; ", self.0, a)?;
        }
        Ok(())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Program -- A full configuration sequence
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Program -- A sequence of field operations
///
/// A program represents the sequence of operations on fields that perform the configuration
/// sequence.
#[derive(Clone, PartialEq, Eq, Hash)]
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
        args: &[Rc<VelosiAstParam>],
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
        let mut f = Function::new(fnname.to_string(), model::types::model());
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
    ///
    /// XXX: this doesn't account for two independent actions on the same field that
    ///      need to be taken.
    pub fn merge(mut self, other: &Self) -> Self {
        // merge the two programs by combining the field actions
        let mut field_operations: HashMap<Arc<String>, Vec<FieldOp>> = HashMap::new();

        log::debug!("MERGE:");
        log::debug!("  {:?}", self);
        log::debug!("  {:?}", other);

        // struct FieldActions(Arc<String>, Vec<Arc<FieldOp>>);
        for op in self.0.iter() {
            if let Some(x) = field_operations.get_mut(&op.0) {
                // insert the field actions into the map by extending the current one
                x.extend(op.1.clone());
            } else {
                // simply insert all actions of the current one
                field_operations.insert(op.0.clone(), op.1.clone());
            }
        }

        for op in other.0.iter() {
            if let Some(existing_ops) = field_operations.get_mut(&op.0) {
                // merge the field actions, for all other actions just insert the ones that
                for other_op in op.1.iter() {
                    use FieldOp::*;
                    // if the new op is basically writing the entire field, then don't do anything
                    if matches!(other_op, InsertField(_) | ReadAction) {
                        continue;
                    }

                    if existing_ops.len() > 2 {
                        panic!("handle me: too many operations on a field");
                    }

                    let last = existing_ops.last_mut().unwrap();
                    match last {
                        InsertField(_) => existing_ops.push(other_op.clone()),
                        ReadAction => existing_ops.push(other_op.clone()),
                        InsertFieldSlices(_) => {
                            last.merge_field_slices(other_op.clone());
                        }
                    }
                }
            } else {
                // simply insert all actions of the current one
                field_operations.insert(op.0.clone(), op.1.clone());
            }
        }

        // by now we should have all field programs ready

        for fop in self.0.iter_mut() {
            let fld = fop.0.clone();
            let ops = field_operations.remove(&fld).unwrap();
            *fop = Arc::new(FieldActions(fld.clone(), ops))
        }

        for fop in other.0.iter() {
            if let Some(ops) = field_operations.remove(&fop.0) {
                let fld = fop.0.clone();
                self.0.push(Arc::new(FieldActions(fld, ops)))
            }
        }

        log::debug!("  {:?}", self);
        self
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Program> for Vec<VelosiOperation> {
    fn from(mut prog: Program) -> Self {
        let mut ops: Vec<VelosiOperation> = prog
            .0
            .iter_mut()
            .flat_map(|o| <&FieldActions as std::convert::Into<Vec<VelosiOperation>>>::into(o))
            .collect();
        ops.push(VelosiOperation::Return);
        ops
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for a in self.0.iter() {
            write!(f, "{a}")?;
        }
        writeln!(f)
    }
}

impl Debug for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for a in self.0.iter() {
            write!(f, "{a}")?;
        }
        writeln!(f)
    }
}
