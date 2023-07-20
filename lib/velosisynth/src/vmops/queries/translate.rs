// Velosiraptor Synthesizer
//
//
// MIT License
//
// Copyright (c) 2022,2023 Systopia Lab, Computer Science, University of British Columbia
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

//! Handles Conjunctive Normal Form

// std imports
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use smt2::Term;
use velosiast::ast::{
    VelosiAstExpr, VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIdentifier,
    VelosiAstMethod, VelosiAstTypeInfo, VelosiAstUnitSegment,
};

use crate::{
    model::method::{translate_map_result_name, translate_protect_result_name},
    z3::Z3WorkerPool,
    Program,
};

//use super::queryhelper::{MaybeResult, ProgramBuilder, QueryBuilder};
use super::MaybeResult;

use super::utils;
use super::ProgramBuilder;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Translate Query Builder
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct TranslateQueryBuilder<'a> {
    unit: &'a VelosiAstUnitSegment,
    m_op: Rc<VelosiAstMethod>,
    m_translate: Rc<VelosiAstMethod>,
    no_change: bool,
}

impl<'a> TranslateQueryBuilder<'a> {
    pub fn new(
        unit: &'a VelosiAstUnitSegment,
        m_op: Rc<VelosiAstMethod>,
        m_translate: Rc<VelosiAstMethod>,
    ) -> Self {
        Self {
            unit,
            m_op,
            m_translate,
            no_change: false,
        }
    }

    /// set the goal of the expression that the query must not change
    pub fn no_change(mut self) -> Self {
        self.no_change = true;
        self
    }

    pub fn build(self) -> Option<TranslateQuery> {
        let body = self.m_translate.body.as_ref().unwrap();
        let mut builder = if self.no_change {
            utils::make_program_builder(self.unit, self.m_op.as_ref(), body)
        } else {
            utils::make_program_builder_no_params(self.unit, body)
        };

        // add the source and destination addresses
        if self.m_op.get_param("va").is_some() {
            builder.add_var(String::from("va"));
        }

        if self.m_op.get_param("pa").is_some() {
            builder.add_var(String::from("pa"));
        }

        let programs = builder.into_iter();
        if programs.has_programs() {
            let (ident, mut args) = match self.m_op.ident().as_str() {
                "map" => (
                    VelosiAstIdentifier::from(translate_map_result_name(None).as_str()),
                    Vec::new(),
                ),
                "protect" => (
                    VelosiAstIdentifier::from(translate_protect_result_name(None).as_str()),
                    Vec::new(),
                ),
                err => panic!("Unknown method {}", err),
            };

            args.push(Rc::new(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("va".to_string(), VelosiAstTypeInfo::VirtAddr),
            )));

            args.push(Rc::new(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("sz".to_string(), VelosiAstTypeInfo::Size),
            )));

            args.push(Rc::new(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("flgs".to_string(), VelosiAstTypeInfo::Flags),
            )));

            args.push(Rc::new(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("pa".to_string(), VelosiAstTypeInfo::PhysAddr),
            )));

            let mut fn_call = VelosiAstFnCallExpr::new(ident, VelosiAstTypeInfo::Bool);
            fn_call.add_args(args);

            let assms = Rc::new(Vec::new());

            Some(TranslateQuery {
                programs: programs.into(),
                assms,
                m_op: self.m_op,
                m_translate: self.m_translate,
                goal: Rc::new(VelosiAstExpr::FnCall(fn_call)),
            })
        } else {
            None
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Translate Query
////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct TranslateQuery {
    /// the programs that this query builder handles
    programs: Box<dyn ProgramBuilder>,
    assms: Rc<Vec<Term>>,
    m_op: Rc<VelosiAstMethod>,
    m_translate: Rc<VelosiAstMethod>,
    goal: Rc<VelosiAstExpr>,
}

impl TranslateQuery {}

impl ProgramBuilder for TranslateQuery {
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
        self.goal.clone()
    }

    fn do_fmt(&self, f: &mut Formatter<'_>, indent: usize, debug: bool) -> FmtResult {
        let i = " ".repeat(indent);
        writeln!(
            f,
            "{i}  + TranslateQuery {}",
            self.m_translate.body.as_ref().unwrap()
        )?;
        self.programs.do_fmt(f, indent + 4, debug)
    }
}

/// Implement `From` for `ProgramVerifier
///
/// To allow conversions from ProgramVerifier -> Box<dyn ProgramBuilder>
impl From<TranslateQuery> for Box<dyn ProgramBuilder> {
    fn from(q: TranslateQuery) -> Self {
        Box::new(q)
    }
}

impl Display for TranslateQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, false)
    }
}

impl Debug for TranslateQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> FmtResult {
        self.do_fmt(f, 0, true)
    }
}
