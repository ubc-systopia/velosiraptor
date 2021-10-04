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

//! State Ast Node

// used standard library functionality
use std::fmt::{Debug, Display, Formatter, Result};

// used library internal functionality
use crate::ast::{utils, AstNode, Field, Issues, SymbolTable};
use crate::error::{ErrorLocation, VrsError};
use crate::token::TokenStream;

/// Defines the state of a translation unit
///
/// The State defines how the translation unit will translate incoming addresses.
/// There are three fundamental state types:
///   - Memory: the state is *external* to the translation unit in some memory (e.g, RAM)
///   - Register: the state is *internal* to the translation unit
///   - None: there is no state associated with it.
#[derive(PartialEq, Clone)]
pub enum State {
    /// defines a memory state (external to the unit)
    MemoryState {
        /// a list of identifiers referring to memory regions
        bases: Vec<String>,
        /// defines a list of fields within the memory regions, defined by the bases
        fields: Vec<Field>,
        /// position where this state was defined
        pos: TokenStream,
    },
    /// defines a register state (internal to the unit)
    RegisterState {
        /// defines a list of fields that form the state
        fields: Vec<Field>,
        /// the position where the state is defined
        pos: TokenStream,
    },
    // TODO state that may be combined
    //CombinedState {  },
    /// No state associated with this translation unit
    None {
        /// the position where the state is defined
        pos: TokenStream,
    },
}

impl State {
    /// builds the symboltable for the state related symbols
    pub fn build_symboltable(&self, st: &mut SymbolTable) {
        for f in self.fields() {
            f.build_symboltable(st);
        }
    }

    /// returns a slice of fields
    pub fn fields(&self) -> &[Field] {
        match self {
            State::MemoryState { fields, .. } => fields,
            State::RegisterState { fields, .. } => fields,
            _ => &[],
        }
    }
}

/// implementation of the [Display] trait for the [State]
impl Display for State {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::State::*;
        match self {
            MemoryState {
                bases,
                fields,
                pos: _,
            } => {
                write!(f, "State(Memory) [")?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos: _ } => {
                writeln!(f, "State(Registers) {{")?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None { pos: _ } => writeln!(f, "State(None)"),
        }
    }
}

/// implementation of the [Debug] trait for the [State]
impl Debug for State {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use self::State::*;
        //let (line, column) = self.pos.input_pos();
        match self {
            MemoryState { bases, fields, pos } => {
                let line = pos.line();
                let column = pos.column();
                write!(f, "{:03}:{:03} | State(Memory) [", line, column)?;
                bases
                    .iter()
                    .fold(Ok(()), |result, b| result.and_then(|_| write!(f, "{} ", b)))?;
                writeln!(f, "] {{")?;

                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            RegisterState { fields, pos } => {
                let line = pos.line();
                let column = pos.column();
                writeln!(f, "{:03}:{:03} | State(Registers) {{", line, column)?;
                fields.iter().fold(Ok(()), |result, field| {
                    result.and_then(|_| writeln!(f, "{}", field))
                })?;
                writeln!(f, "}}")
            }
            None { pos } => {
                let line = pos.line();
                let column = pos.column();
                writeln!(f, "{:03}:{:03} | State(None)", line, column)
            }
        }
    }
}

/// implementation of [AstNode] for [State]
impl AstNode for State {
    fn check(&self, st: &mut SymbolTable) -> Issues {
        let mut res = Issues::ok();

        // extract the fields and bases from the  state
        let (fields, bases) = match self {
            State::MemoryState {
                bases,
                fields,
                pos: _,
            } => (fields, Some(bases)),
            State::RegisterState { fields, pos: _ } => (fields, None),
            State::None { pos: _ } => {
                return Issues::ok();
            }
        };

        // Check 1: Fields
        // --------------------------------------------------------------------------------------
        // Type:        Error/Warning
        // Description: Check all fields of the state
        // Notes:
        // --------------------------------------------------------------------------------------
        for f in fields {
            res = res + f.check(st)
        }

        // Check 2: Double defined fields
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all BitSlices of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let errors = utils::check_double_entries(fields);
        res.inc_err(errors);

        // Check 3: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check if the fields have all defined bases
        // Notes:       --
        // --------------------------------------------------------------------------------------

        match bases {
            Some(bases) => {
                for f in fields {
                    if let Some(sref) = &f.stateref {
                        // case 1: we have a state ref
                        let (sref, _) = sref;
                        // if the bases list contain a state ref, we're good
                        if bases.contains(sref) {
                            continue;
                        }
                        // undefined base
                        let msg = format!("field `{}` has invalid state ref", f.name());
                        let hint =
                            format!("add state reference here. One of `{}`", bases.join("`, `"));
                        VrsError::new_err(f.loc().with_range(1..2), msg, Some(hint)).print();
                        res.inc_err(1);
                    } else {
                        // no state ref, but required one
                        let msg = format!("field `{}` has missing state reference", f.name());
                        let hint =
                            format!("add state reference here. One of `{}`", bases.join("`, `"));
                        VrsError::new_err(f.loc().with_range(1..2), msg, Some(hint)).print();
                        res.inc_err(1);
                    }
                }
            }
            None => {
                for f in fields {
                    if f.stateref.is_some() {
                        // state ref found, but none required
                        let msg = format!(
                            "field `{}` contains state reference, but state has none.",
                            f.name()
                        );
                        let hint = String::from("remove the state reference in the field");
                        VrsError::new_err(f.loc().with_range(1..2), msg, Some(hint)).print();
                        res.inc_err(1);
                    }
                }
            }
        }

        // Check 4: No bases defined double
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check if the bases are not double defined
        // Notes:       --
        // --------------------------------------------------------------------------------------
        match bases {
            Some(bases) => {
                let mut s = bases.clone();
                s.sort();
                s.dedup();
                if s.len() < bases.len() {
                    let msg = String::from("double defined bases in state definition");
                    VrsError::new_err(self.loc().with_range(1..2), msg, None).print();
                    res.inc_err(1);
                    res
                } else {
                    res
                }
            }
            _ => res,
        }
    }

    fn name(&self) -> &str {
        "State"
    }

    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        use self::State::*;
        match self {
            MemoryState {
                bases: _,
                fields: _,
                pos,
            } => pos,
            RegisterState { fields: _, pos } => pos,
            None { pos } => pos,
        }
    }
}
