// Velosiraptor ParseTree
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

//! Ast Module of the Velosiraptor Compiler

use std::collections::{HashMap, HashSet};

use crate::ast::{AstNodeGeneric, Expr, Issues, SymbolTable};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Defines an action that is executed on the interface
///
/// An action defines a read access to the state or a write access to the state. The latter
/// basically triggers a state transition.
///
/// Currently an action is basically an assignment that assigns the destination the value of the
/// source. If the destination is a StateRef, then this
///   src => dst
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ActionComponent {
    /// the source operand of the action
    pub src: Expr,
    /// the destination operand of the action
    pub dst: Expr,
    /// the location where the action was defined
    pub pos: TokenStream,
}

impl<'a> ActionComponent {
    pub fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // Check 1: Validate Source and Destination Expressions
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Errors
        // Description: Check if the expressions are well defined
        // Notes:       --
        // --------------------------------------------------------------------------------------
        let mut res = self.src.check(st) + self.dst.check(st);

        // Check 2: The destination must be an lvalue
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if the destination is an lvalue
        // Notes:       --
        // --------------------------------------------------------------------------------------
        if !self.dst.is_lvalue() {
            let msg = String::from("invalid left-hand side of assignment");
            let hint = String::from("cannot assign to this expression");

            VrsError::new_err(&self.pos, msg, Some(hint)).print();
            res.inc_err(1);
        }

        // Check 3: The destination must be an identifier
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if the destination is an identifier
        // Notes:       We currently don't support slices here
        // --------------------------------------------------------------------------------------
        let src_is_state = match &self.dst {
            Expr::Identifier { path, .. } => Some(path[0] == "state"),
            Expr::Slice { path, .. } => {
                let msg = String::from("invalid left-hand side of assignment");
                let hint = String::from("slice expressions are not yet supported");
                VrsError::new_err(&self.pos, msg, Some(hint)).print();
                res.inc_err(1);
                Some(path[0] == "state")
            }
            Expr::Element { path, .. } => {
                let msg = String::from("invalid left-hand side of assignment");
                let hint = String::from("array element expressions are not yet supported");
                VrsError::new_err(&self.pos, msg, Some(hint)).print();
                res.inc_err(1);
                Some(path[0] == "state")
            }
            _ => {
                let msg = String::from("invalid left-hand side of assignment");
                let hint = format!("not supported expression: {}", self.dst);
                VrsError::new_err(&self.pos, msg, Some(hint)).print();
                res.inc_err(1);
                None
            }
        };

        // Check 4: The source type is ok
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: The source type should be an identifier
        // Notes:       We currently don't support more complex expressions as of yet
        // --------------------------------------------------------------------------------------

        let dst_is_state = match &self.src {
            Expr::Identifier { path, .. } => Some(path[0] == "state"),
            Expr::Number { .. } => Some(false),
            Expr::Boolean { .. } => Some(false),
            _ => {
                if !self.src.is_const_expr(st) {
                    let msg = String::from("invalid right-hand side of assignment");
                    let hint = format!("not supported expression: {}", self.src);
                    VrsError::new_err(&self.pos, msg, Some(hint)).print();
                    res.inc_err(1);
                }
                None
            }
        };

        // Check 5: Check whether the data flow is valid
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: The source and destination must be
        // Notes:       --
        // --------------------------------------------------------------------------------------
        if let (Some(a), Some(b)) = (src_is_state, dst_is_state) {
            if a == b {
                let msg = String::from("invalid assignment");
                let hint = String::from("can only move interface -> state or state -> interface");
                VrsError::new_err(&self.pos, msg, Some(hint)).print();
                res.inc_err(1);
            }
        }

        // Check 6: No bit overflow (TODO)
        // --------------------------------------------------------------------------------------
        // Type:        Errors
        // Description: Check if the destination bits can hold the source bits
        // Notes:       --
        // --------------------------------------------------------------------------------------

        // TODO

        res
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
    pub fn handle_state_access_dst(
        &'a self,
        state_syms: &HashSet<String>,
        state_bits: &HashMap<String, u64>,
        if_bits: &HashMap<String, u64>,
    ) -> HashSet<String> {
        let dst_refs = self.dst.get_state_references();
        if dst_refs.is_empty() {
            // there were no stare references
            return HashSet::new();
        }

        let src_refs = self.src.get_interface_references();
        if src_refs.is_empty() {
            // there were no interface references
            return HashSet::new();
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
                let bits = state_bits.get(dst_ref).unwrap();
                for (fld, b) in if_bits {
                    if bits & b != 0 {
                        res.insert(fld.clone());
                    } else {
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

/// Represents the type of action
///
/// Currently the only supported action types are Read and Write but, we can imagine needing more
/// types to support custom instructions needing to be executed to dump state to memory.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ActionType {
    Read,
    Write,
}

/// Defines the collection of Action components that occur when a Read/Write operation is
/// executed.
///
/// i.e:
/// WriteAction {
///     interface.size.npages => state.size.npages;
///     1 => state.valid;
///     0 => state.cache;
///     1 => interface.status;
/// }
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Action {
    /// the type of the action (Read/Write)
    pub action_type: ActionType,
    /// the list of action components that are associated with this action
    pub action_components: Vec<ActionComponent>,
    /// the location where the action was defined
    pub pos: TokenStream,
}

impl Action {
    pub fn accessing_state(
        &self,
        state_syms: &HashSet<String>,
        state_bits: &HashMap<String, u64>,
        if_bits: &HashMap<String, u64>,
    ) -> HashSet<String> {
        let mut res = HashSet::new();
        for ac in &self.action_components {
            // this is just a single action component here
            // e.g., interface.field.slice -> state.field.slice;

            // There are multiple ways to access the field here
            //   state.field
            //   state.field.slice
            //
            //   Not yet supported:
            //   state.field[0]
            //   state.field.slice[0]
            //   state.field[0..1]
            //   state.field.slice[0..1]

            res.extend(ac.handle_state_access_dst(state_syms, state_bits, if_bits));
        }
        res
    }
}
