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
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result};

// used library internal functionality
use crate::ast::{
    utils, AstNode, AstNodeGeneric, Field, Issues, Param, Symbol, SymbolKind, SymbolTable, Type,
    TOKENSTREAM_DUMMY,
};
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
        bases: Vec<Param>,
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
    None { pos: TokenStream },
}

pub const NONE_STATE: State = State::None {
    pos: TOKENSTREAM_DUMMY,
};

impl<'a> State {
    pub fn new_none() -> Self {
        State::None {
            pos: TokenStream::empty(),
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, State::None { .. })
    }

    pub fn is_memory(&self) -> bool {
        matches!(self, State::MemoryState { .. })
    }

    /// builds the symboltable for the state related symbols
    pub fn build_symboltable(&'a self, st: &mut SymbolTable<'a>) {
        // create the 'state' symbol
        let sym = Symbol::new(
            String::from("state"),
            Type::State,
            SymbolKind::State,
            self.loc().clone(),
            AstNode::State(self),
        );
        st.insert(sym);

        for f in self.fields() {
            f.build_symboltable(st);
        }
    }

    /// returns the number of fields in the state
    pub fn nfields(&self) -> usize {
        self.fields().len()
    }

    /// returns a slice of fields
    pub fn fields(&self) -> &[Field] {
        match self {
            State::MemoryState { fields, .. } => fields,
            State::RegisterState { fields, .. } => fields,
            _ => &[],
        }
    }

    pub fn bases(&self) -> &[Param] {
        match self {
            State::MemoryState { bases, .. } => bases.as_slice(),
            _ => &[],
        }
    }

    pub fn referenced_field_bits(&self, refs: &HashSet<String>) -> HashMap<String, u64> {
        let mut hs = HashMap::new();
        for f in self.fields() {
            let n = format!("state.{}", f.name);
            hs.insert(n, f.referenced_field_bits(refs));
        }
        hs
    }
}

impl Default for State {
    fn default() -> Self {
        State::None {
            pos: TokenStream::empty(),
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
            None { .. } => writeln!(f, "State(None)"),
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

/// implementation of [AstNodeGeneric] for [State]
impl<'a> AstNodeGeneric<'a> for State {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        // extract the fields and bases from the  state

        if let State::None { .. } = self {
            return Issues::ok();
        }

        let fields = self.fields();
        let bases = self.bases();

        // create a new symtable context, this is required for base checking in the fields
        st.create_context(String::from("state"));

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

        // Check 3: Double defined bases
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check that all bases of this field have distinct names
        // Notes:       --
        // --------------------------------------------------------------------------------------
        let errors = utils::check_double_entries(bases);
        res.inc_err(errors);

        // Check 4: Bases are defined on unit level
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check if the defined bases are in fact valid
        // Notes:       --
        // --------------------------------------------------------------------------------------
        for b in bases {
            let sym = st.lookup(&b.name);
            if let Some(sym) = sym {
                if sym.kind != SymbolKind::Parameter {
                    VrsError::new_double_kind(
                        String::from(b.name()),
                        b.loc().with_range(0..2),
                        sym.loc.with_range(0..2),
                    )
                    .print();
                    res.inc_err(1);
                }

                if !sym.typeinfo.compatible(b.ptype) {
                    VrsError::new_double_type(
                        String::from(b.name()),
                        b.loc().with_range(0..2),
                        sym.loc.with_range(0..2),
                    )
                    .print();
                    res.inc_err(1);
                }
            } else {
                // undefined base
                let msg = format!(
                    "state base `{}` has not been defined on unit level",
                    b.name()
                );
                let hint = format!("add `{} : {}` to the unit parameters", b.name, b.ptype);
                VrsError::new_err(b.loc(), msg, Some(hint)).print();
                res.inc_err(1);

                // insert the symbol, so we won't throw an error in the field level
                st.insert(b.to_symbol());
            }
        }

        // Check 5: Bases are defined
        // --------------------------------------------------------------------------------------
        // Type:        Error
        // Description: Check if the fields have all defined bases
        // Notes:       --
        // --------------------------------------------------------------------------------------

        let stateref_required = matches!(self, State::MemoryState { .. });

        for f in fields {
            if f.stateref.is_none() && stateref_required {
                // no state ref, but required one
                let msg = format!("field `{}` has missing state reference", f.name());
                let hint = format!("add state reference here. One of `{:?}`", bases);
                VrsError::new_err(f.loc().with_range(1..2), msg, Some(hint)).print();
                res.inc_err(1);
            }
            if f.stateref.is_some() && !stateref_required {
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

        // drop the symbol table context again
        st.drop_context();

        res
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
