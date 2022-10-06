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

use crate::ast::{
    utils, Action, ActionType, AstNode, AstNodeGeneric, Field, Issues, Param, Symbol, SymbolKind,
    SymbolTable, Type, TOKENSTREAM_DUMMY,
};
use crate::error::VrsError;
use crate::token::TokenStream;

/// Defines the software-visible interface of a unit
///
/// Similar to the state, there are multiple options of the interface:
///   - Memory: load/store to memory (normal DRAM)
///   - MMIORegisters: load/store to memory-mapped device registers
///   - CPURegisters: load/store to CPU registers
///   - SpecialRegisters: use of special instructions (no load/store) to those
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Interface {
    /// Defines a load/store interface to memory
    Memory {
        bases: Vec<Param>,
        fields: Vec<InterfaceField>,
        pos: TokenStream,
    },
    /// Defines a memory-mapped interface to registers
    MMIORegisters {
        bases: Vec<Param>,
        fields: Vec<InterfaceField>,
        pos: TokenStream,
    },
    /// Defines a load/store interface to CPU registers
    CPURegisters {
        fields: Vec<InterfaceField>,
        pos: TokenStream,
    },
    /// Defines a register interface using special instructions
    SpecialRegisters { pos: TokenStream },
    // TODO interface may be a combination: e.g., Memory + MMIORegisters
    //CombinedState {  },
    /// No software interface associated with this translation unit
    None { pos: TokenStream },
}

pub const NONE_INTERFACE: Interface = Interface::None {
    pos: TOKENSTREAM_DUMMY,
};

/// Implementation of the Interface
impl<'a> Interface {
    pub fn new_none() -> Self {
        Interface::None {
            pos: TokenStream::empty(),
        }
    }

    /// builds the symboltable for the interface related symbols
    pub fn build_symboltable(&'a self, st: &mut SymbolTable<'a>) {
        // create the 'interface' symbol
        let sym = Symbol::new(
            String::from("interface"),
            Type::Interface,
            SymbolKind::Interface,
            self.loc().clone(),
            AstNode::Interface(self),
        );
        st.insert(sym);

        // foreach field in the interface fields populate the symbol table
        for f in self.fields() {
            f.build_symboltable(st);
        }
    }

    /// returns the number of fields in the state
    pub fn nfields(&self) -> usize {
        self.fields().len()
    }

    pub fn fields(&self) -> &[InterfaceField] {
        match self {
            Interface::CPURegisters { fields, .. } => fields,
            Interface::Memory { fields, .. } => fields,
            Interface::MMIORegisters { fields, .. } => fields,
            Interface::SpecialRegisters { .. } => &[],
            Interface::None { .. } => &[],
        }
    }

    pub fn bases(&self) -> &[Param] {
        match self {
            Interface::CPURegisters { .. } => &[],
            Interface::Memory { bases, .. } => bases,
            Interface::MMIORegisters { bases, .. } => bases,
            Interface::SpecialRegisters { .. } => &[],
            Interface::None { .. } => &[],
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, Interface::None { .. })
    }

    pub fn is_register(&self) -> bool {
        matches!(self, Interface::MMIORegisters { .. })
    }

    pub fn field_by_name(&self, name: &str) -> Option<&InterfaceField> {
        self.fields().iter().find(|f| f.name() == name)
    }

    // returns a list of all the fields with action that touch one of the state elements
    pub fn fields_accessing_state(
        &self,
        state_syms: &HashSet<String>,
        state_bits: &HashMap<String, u64>,
    ) -> HashSet<String> {
        let mut if_bits = HashMap::new();
        for f in self.fields() {
            for l in &f.field.layout {
                let n = format!("interface.{}.{}", f.field.name, l.name);
                if_bits.insert(n, l.mask_value());
            }
        }

        let mut hs = HashSet::new();
        for f in self.fields() {
            let fhs = f.accessing_state(state_syms, state_bits, &if_bits);
            hs.extend(fhs)
        }
        hs
    }
}

impl Default for Interface {
    fn default() -> Self {
        Interface::None {
            pos: TokenStream::empty(),
        }
    }
}

/// Implementation of [AstNodeGeneric] for [Interface]
impl<'a> AstNodeGeneric<'a> for Interface {
    // checks the node and returns the number of errors and warnings encountered
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // TODO: Implement the checks, this may follow a similar structure as the state
        let mut res = Issues::ok();

        // extract the fields and bases from the state
        let fields = self.fields();
        let bases = self.bases();

        // create a new symtable context, this is required for base checking in the fields
        st.create_context(String::from("interface"));

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
                if sym.kind != SymbolKind::Parameter || !sym.typeinfo.compatible(b.ptype) {
                    VrsError::new_double_kind(
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
                    "interface base `{}` has not been defined on unit level",
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
        let stateref_required = matches!(self, Interface::Memory { .. })
            || matches!(self, Interface::MMIORegisters { .. });

        for f in fields {
            if f.field.stateref.is_none() && stateref_required {
                // no state ref, but required one
                let msg = format!("field `{}` has missing state reference", f.name());
                let hint = format!("add state reference here. One of `{:?}`", bases);
                VrsError::new_err(f.loc().with_range(1..2), msg, Some(hint)).print();
                res.inc_err(1);
            }
            if f.field.stateref.is_some() && !stateref_required {
                // state ref found, but none required
                let msg = format!(
                    "field `{}` contains state reference, but interface has none.",
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

    /// returns a printable string representing the ast node
    fn name(&self) -> &str {
        "interface"
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        match self {
            Interface::CPURegisters { pos, .. } => pos,
            Interface::Memory { pos, .. } => pos,
            Interface::MMIORegisters { pos, .. } => pos,
            Interface::SpecialRegisters { pos, .. } => pos,
            Interface::None { pos, .. } => pos,
        }
    }
}

/// Defines a field in the interface
///
/// A field may represent a 8, 16, 32, 64 bit region in the state with a
/// specific bit layout and an additional collection of  actions.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct InterfaceField {
    // The field itself
    pub field: Field,
    // The ReadAction for this field
    pub readaction: Option<Action>,
    // The WriteAction for this field,
    pub writeaction: Option<Action>,
}

/// Implementation for the InterfaceField
impl<'a> InterfaceField {
    /// converts the field into a symbol
    pub fn to_symbol(&self) -> Symbol {
        // prepend the 'state' prefix
        let name = format!("interface.{}", self.field.name);
        Symbol::new(
            name,
            Type::Integer,
            SymbolKind::State,
            self.field.pos.clone(),
            AstNode::InterfaceField(self),
        )
    }

    pub fn build_symboltable(&'a self, st: &mut SymbolTable<'a>) {
        st.insert(self.to_symbol());

        for s in &self.field.layout {
            let name = format!("interface.{}.{}", self.field.name, s.name);
            st.insert(Symbol::new(
                name,
                Type::Integer,
                SymbolKind::State,
                s.loc().clone(),
                AstNode::BitSlice(s),
            ));
        }
    }

    pub fn accessing_state(
        &'a self,
        state_syms: &HashSet<String>,
        state_bits: &HashMap<String, u64>,
        if_bits: &HashMap<String, u64>,
    ) -> HashSet<String> {
        let mut res = HashSet::new();

        res.extend(
            self.readaction
                .as_ref()
                .map(|a| a.accessing_state(state_syms, state_bits, if_bits))
                .unwrap_or_default(),
        );

        res.extend(
            self.writeaction
                .as_ref()
                .map(|a| a.accessing_state(state_syms, state_bits, if_bits))
                .unwrap_or_default(),
        );

        res
    }
}

/// Implementation of [AstNodeGeneric] for [InterfaceField]
impl<'a> AstNodeGeneric<'a> for InterfaceField {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        let mut res = Issues::ok();

        // Check 1: Validate Field
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Errors
        // Description: Check that the Field is valid
        // Notes:       --
        // --------------------------------------------------------------------------------------
        res = res + self.field.check(st);

        // Check 2: Validate Read Action
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Errors
        // Description: Check that the Read Action is valid
        // Notes:       For now we can just allow numbers and identifiers for src. dst must be an
        //              idents
        // --------------------------------------------------------------------------------------
        match &self.readaction {
            Some(read_action) => {
                // Make sure it's a read action
                assert_eq!(read_action.action_type, ActionType::Read);
                for action_component in &read_action.action_components {
                    // Verify the action component
                    action_component.check(st);
                }
            }
            None => {}
        }

        // Check 3: Validate Write Action
        // --------------------------------------------------------------------------------------
        // Type:        Warning/Errors
        // Description: Check that the Write Action is valid
        // Notes:       --
        // --------------------------------------------------------------------------------------
        match &self.writeaction {
            Some(write_action) => {
                // Make sure it's a write action
                assert_eq!(write_action.action_type, ActionType::Write);
                for action_component in &write_action.action_components {
                    // Verify the action component
                    action_component.check(st);
                }
            }
            None => {}
        }

        res
    }

    /// returns a printable string representing the ast node
    fn name(&self) -> &str {
        self.field.name()
    }

    /// returns the location of the AstNodeGeneric
    fn loc(&self) -> &TokenStream {
        self.field.loc()
    }
}
