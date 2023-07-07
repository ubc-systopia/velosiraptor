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
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// library imports
use smt2::Term;
use velosiast::ast::{
    VelosiAstExpr, VelosiAstMethod, VelosiAstUnOp, VelosiAstUnOpExpr, VelosiAstUnitSegment,
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
    mem_model: Option<Program>,
    /// whether or not to allow variable references
    variable_references: bool,
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
            variable_references: false,
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
    pub fn mem_model(mut self, prog: Program) -> Self {
        self.mem_model = Some(prog);
        self
    }

    /// whether we want to allow variable references in the pre-conditions
    pub fn variable_references(mut self) -> Self {
        self.variable_references = true;
        self
    }

    pub fn programs(mut self, programs: Box<dyn ProgramBuilder>) -> Self {
        self.programs = Some(programs);
        self
    }

    /// builds the bool expr query or returns None if there are no queries to be run
    pub fn build(self) -> Option<BoolExprQuery> {
        // if the expression doesn't have state references, then nothing to be done.
        if !self.goal_expr.has_state_references() {
            log::info!("No state references in the expression");
            return None;
        }

        // check if the expression has variable references and we want variable referenes
        let params = self.m_op.get_param_names();
        if self.goal_expr.has_var_references(&params) != self.variable_references {
            return None;
        }

        let mem_model = self.mem_model.is_some();

        // We either spec
        let programs = if let Some(programs) = self.programs {
            programs
        } else if let Some(prog) = self.mem_model {
            Box::new(utils::make_program_iter_mem(prog))
        } else {
            let programs =
                utils::make_program_builder(self.unit, self.m_op.as_ref(), &self.goal_expr)
                    .into_iter();
            if !programs.has_programs() {
                return None;
            }
            Box::new(programs)
        };

        // convert the goal expression if needed
        let expr = if self.negate {
            let loc = self.goal_expr.loc().clone();
            Rc::new(VelosiAstExpr::UnOp(VelosiAstUnOpExpr::new(
                VelosiAstUnOp::LNot,
                self.goal_expr,
                loc,
            )))
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
