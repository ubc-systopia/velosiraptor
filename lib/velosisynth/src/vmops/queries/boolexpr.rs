// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2023 Systopia Lab, Computer Science, University of British Columbia
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

//! Boolean Expressions

// std imports
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// library imports
use smt2::Term;
use velosiast::ast::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstExpr, VelosiAstMethod, VelosiAstUnOp,
    VelosiAstUnOpExpr, VelosiAstUnitSegment,
};

// crate imports
use crate::{z3::Z3WorkerPool, Program};

//use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};
use super::MaybeResult;
use super::ProgramBuilder;

use super::utils;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Boolean Expression Builder
////////////////////////////////////////////////////////////////////////////////////////////////////

/// builds a boolean expression query
pub struct BoolExprQueryBuilder<'a> {
    /// the unit context for this query
    unit: &'a VelosiAstUnitSegment,
    /// the programs that this query builder handles
    goal_expr: Rc<VelosiAstExpr>,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// assumptions for the boolean expressions
    assms: Rc<Vec<Term>>,
    /// whether or not to negate the expression
    negate: bool,
    /// whether to specialize the program for memory model
    mem_model: Option<Rc<Program>>,
    /// whether or not to allow variable references
    variable_references: Option<bool>,
    /// additional state refs
    state_refs: Option<HashSet<Rc<String>>>,
    /// programs generator
    programs: Option<Box<dyn ProgramBuilder>>,
}

impl<'a> BoolExprQueryBuilder<'a> {
    /// creates a builder for boolean expression queries
    pub fn new(
        unit: &'a VelosiAstUnitSegment,
        m_op: Rc<VelosiAstMethod>,
        goal_expr: Rc<VelosiAstExpr>,
    ) -> Self {
        Self {
            unit,
            goal_expr,
            m_op,
            assms: Rc::new(Vec::new()),
            negate: false,
            mem_model: None,
            variable_references: None,
            state_refs: None,
            programs: None,
        }
    }

    /// sets the assumptions for the supplied vector
    pub fn assms(mut self, assms: Rc<Vec<Term>>) -> Self {
        self.assms = assms;
        self
    }

    /// whether or not to negate the expression
    pub fn negate(mut self, toggle: bool) -> Self {
        self.negate = toggle;
        self
    }

    /// sets the memory model to be used
    pub fn mem_model(mut self, prog: Rc<Program>) -> Self {
        self.mem_model = Some(prog);
        self
    }

    /// whether we want to allow variable references in the pre-conditions
    pub fn variable_references(mut self, var_refs: bool) -> Self {
        self.variable_references = Some(var_refs);
        self
    }

    pub fn additional_state_refs(mut self, state_refs: HashSet<Rc<String>>) -> Self {
        self.state_refs = Some(state_refs);
        self
    }

    pub fn programs(mut self, programs: Box<dyn ProgramBuilder>) -> Self {
        self.programs = Some(programs);
        self
    }

    /// builds the bool expr query or returns None if there are no queries to be run
    pub fn build(self) -> Option<BoolExprQuery> {
        // if the expression doesn't have state references, then nothing to be done.
        let has_state_refs = self.goal_expr.has_state_references() || self.goal_expr.is_fncall();

        if !has_state_refs && self.mem_model.is_none() {
            log::info!("No state references in the expression");
            return None;
        }

        // check if the expression has variable references and we want variable referenes
        let params = self.m_op.get_param_names();
        let has_var_refs = self.goal_expr.has_var_references(&params);
        if let Some(var_refs) = &self.variable_references {
            if has_var_refs != *var_refs {
                return None;
            }
        }

        let mem_model = self.mem_model.is_some();

        // construct the program builder for the expression
        let programs = if let Some(programs) = self.programs {
            // just use the supplied program if we have one
            programs
        } else if let Some(prog) = self.mem_model {
            // if we are dealing with a memory model we already have the program, so
            // specialize it
            Box::new(utils::make_program_iter_mem(&prog))
        } else {
            // construct the program builder
            let programs = utils::make_program_builder(
                self.unit,
                self.m_op.as_ref(),
                &self.goal_expr,
                self.state_refs.unwrap_or_default(),
            )
            .into_iter();
            if !programs.has_programs() {
                return None;
            }
            Box::new(programs)
        };

        // negate the goal expressions if we need to
        let expr = if self.negate {
            match self.goal_expr.as_ref() {
                VelosiAstExpr::UnOp(VelosiAstUnOpExpr {
                    op: VelosiAstUnOp::LNot,
                    expr,
                    ..
                }) => {
                    // if we have double negation simply remove it
                    expr.clone()
                }
                _ => {
                    // negate the expression
                    let loc = self.goal_expr.loc().clone();
                    Rc::new(VelosiAstExpr::UnOp(VelosiAstUnOpExpr::new(
                        VelosiAstUnOp::LNot,
                        self.goal_expr,
                        loc,
                    )))
                }
            }
        } else {
            self.goal_expr
        };

        Some(BoolExprQuery {
            programs,
            m_op: self.m_op,
            assms: self.assms,
            expr,
            mem_model,
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Boolean Expression Query
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct BoolExprQuery {
    /// the programs that this query builder handles
    programs: Box<dyn ProgramBuilder>,
    /// the operation method
    m_op: Rc<VelosiAstMethod>,
    /// assumptions we want to run the query with
    assms: Rc<Vec<Term>>,
    /// the boolean expression to be evaluated
    expr: Rc<VelosiAstExpr>,
    /// whether to use the memory model
    mem_model: bool,
}

impl ProgramBuilder for BoolExprQuery {
    fn next(&mut self, z3: &mut Z3WorkerPool) -> MaybeResult<Program> {
        self.programs.next(z3)
    }

    fn m_op(&self) -> &VelosiAstMethod {
        self.m_op.as_ref()
    }

    /// the assumptions for the program
    fn assms(&self) -> Rc<Vec<Term>> {
        self.assms.clone()
    }

    /// the expression that the program needs to establish
    fn goal_expr(&self) -> Rc<VelosiAstExpr> {
        self.expr.clone()
    }

    fn mem_model(&self) -> bool {
        self.mem_model
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(f, "{i} - BoolExprQuery( assms ==> {} )", self.goal_expr())?;
        self.programs.do_fmt(f, indent + 2, debug)
    }
}

/// Implement `From` for `BoolExprQuery`
///
/// To allow conversions from BoolExprQuery -> Box<dyn ProgramBuilder>
impl From<BoolExprQuery> for Box<dyn ProgramBuilder> {
    fn from(q: BoolExprQuery) -> Self {
        Box::new(q)
    }
}

impl Display for BoolExprQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for BoolExprQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
