// VelosiAst -- a Ast for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiAst - Interface Actions
//!
//! This modules defines the actions on the interface fields.

// used standard library functionality
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// used parse tree definitions
use velosiparser::parsetree::VelosiParseTreeInterfaceAction;
use velosiparser::VelosiTokenStream;

// used crate functionality
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, AstResult, SymbolTable};

// used definitions of references AST nodes
use crate::ast::VelosiAstExpr;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Actions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines an action that is executed on the interface
///
/// An action defines a read access to the state or a write access to the state. The latter
/// basically triggers a state transition.
///
/// Currently an action is basically an assignment that assigns the destination the value of the
/// source. If the destination is a StateRef, then this src => dst
#[derive(Eq, Clone)]
pub struct VelosiAstInterfaceAction {
    /// the source operand of the action
    pub src: Rc<VelosiAstExpr>,
    /// the destination operand of the action (lvalue expression)
    pub dst: Rc<VelosiAstExpr>,
    /// the location where the action was defined
    pub loc: VelosiTokenStream,
}

impl VelosiAstInterfaceAction {
    pub fn new(src: Rc<VelosiAstExpr>, dst: Rc<VelosiAstExpr>, loc: VelosiTokenStream) -> Self {
        Self { src, dst, loc }
    }

    pub fn from_parse_tree(
        pt: VelosiParseTreeInterfaceAction,
        st: &mut SymbolTable,
    ) -> AstResult<VelosiAstInterfaceAction, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        let src = Rc::new(ast_result_unwrap!(
            VelosiAstExpr::from_parse_tree(pt.src, st),
            issues
        ));
        let dst = Rc::new(ast_result_unwrap!(
            VelosiAstExpr::from_parse_tree(pt.dst, st),
            issues
        ));

        // the destination must be an lvalue that can be assigned to.
        if !dst.is_lvalue() {
            let msg = format!("Destination of action `{dst}` is not an lvalue");
            let hint = "Convert the expression to an lvalue";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(dst.loc().clone())
                .build();
            issues.push(err);
        }

        // the types must match
        if !dst.result_type().compatible(src.result_type()) {
            let msg = "type mismatch";
            let hint = format!(
                "Cannot assign value of type `{}` to `{}`",
                src.result_type(),
                dst.result_type()
            );
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(dst.loc().clone())
                .build();
            issues.push(err);
        }

        // we can only assign number types for now
        if !src.result_type().is_numeric() {
            let msg = "unsupported type";
            let hint = format!(
                "Expected a numeric or boolean type, but got `{}`",
                src.result_type(),
            );
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(src.loc().clone())
                .build();
            issues.push(err);
        }

        // TODO: check the bit overflow

        ast_result_return!(VelosiAstInterfaceAction::new(src, dst, pt.loc), issues)
    }

    /// handles state accesses with a state reference in the destination
    ///
    /// # Example
    ///
    ///  - `interface.field.slice -> state.field.slice;`
    ///  - `interface.field       -> state.field.slice;`
    ///  - `interface.field.slice -> state.field;`
    ///  - `interface.field       -> state.field;`
    ///  -  `1                    -> state.field.slice;
    ///  -  `1                    -> state.field;
    pub fn get_iface_refs_for_state_update(
        &self,
        state_syms: &HashSet<Rc<String>>,
        state_bits: &HashMap<Rc<String>, u64>,
        if_bits: &HashMap<Rc<String>, u64>,
    ) -> HashSet<Rc<String>> {
        // TODO: here we should build the transitive closure of the
        //       state references. As the state can be update by moving
        //       data from one state field to another.

        let mut dst_refs = HashSet::new();
        self.dst.get_state_references(&mut dst_refs);
        if dst_refs.is_empty() {
            // there were no stare references, return empty
            return dst_refs;
        }

        let mut src_refs = HashSet::new();
        self.src.get_interface_references(&mut src_refs);
        if src_refs.is_empty() {
            // there were no interface references, but we had a state reference
            return src_refs;
        }

        // we should not have multiple state or interface references in an lvalue
        debug_assert!(dst_refs.len() == 1);
        debug_assert!(src_refs.len() == 1);

        let dst_ref = dst_refs.iter().next().unwrap();
        let dst_ref_parts = dst_ref.split('.').collect::<Vec<&str>>();

        debug_assert_eq!(dst_ref_parts[0], "state");

        let src_ref = src_refs.iter().next().unwrap();
        let src_ref_parts = src_ref.split('.').collect::<Vec<&str>>();

        debug_assert_eq!(src_ref_parts[0], "interface");

        match (src_ref_parts.len(), dst_ref_parts.len()) {
            //  - `interface.field.slice -> state.field.slice;`
            (3, 3) => {
                // one-to-one match, we simply take the interface reference here.
                if state_syms.contains(dst_ref) {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field       -> state.field.slice;`
            (2, 3) => {
                //HashSet::new()
                // somehow here we could filter out slices > number of bits...
                if state_syms.contains(dst_ref) {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field.slice -> state.field;`
            (3, 2) => {
                let bits = state_bits.get(dst_ref).unwrap();
                if *bits != 0 {
                    src_refs
                } else {
                    HashSet::new()
                }
            }
            //  - `interface.field       -> state.field;`
            (2, 2) => {
                // add the interface elements that actually match the used state elements.

                let mut res = HashSet::new();
                //res.insert(src_ref.clone());
                let bits = *state_bits.get(dst_ref).unwrap();

                // nothing to be returned here
                if bits == 0 {
                    return res;
                }

                // do the back projection of the bits of the state to the interface
                // loop over the ifbits and pick the slices that matter.
                for (fld, b) in if_bits {
                    if fld.starts_with(src_ref.as_str()) && bits & b != 0 {
                        res.insert(fld.clone());
                    }
                }
                res
            }
            _ => {
                panic!("unsupported state access: {} -> {}", self.src, self.dst);
            }
        }
    }
}

/// Implementation of [PartialEq] for [VelosiAstInterfaceAction]
impl PartialEq for VelosiAstInterfaceAction {
    fn eq(&self, other: &Self) -> bool {
        self.src == other.src && self.dst == other.dst
    }
}

/// implementation of trait [Display] for [VelosiAstInterfaceAction]
impl Display for VelosiAstInterfaceAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} -> {}", self.src, self.dst)
    }
}

/// Implementation of [Debug] for [VelosiAstInterfaceAction]
impl Debug for VelosiAstInterfaceAction {
    fn fmt(&self, format: &mut Formatter) -> FmtResult {
        Display::fmt(&self, format)
    }
}
