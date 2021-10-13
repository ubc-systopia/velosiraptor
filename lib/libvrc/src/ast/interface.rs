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

use crate::ast::{Expr, Field, Param};
use crate::token::TokenStream;

/// Defines the software-visible interface of a unit
///
/// Similar to the state, there are multiple options of the interface:
///   - Memory: load/store to memory (normal DRAM)
///   - MMIORegisters: load/store to memory-mapped device registers
///   - CPURegisters: load/store to CPU registers
///   - SpecialRegisters: use of special instructions (no load/store) to those
#[derive(PartialEq, Clone)]
pub enum Interface {
    /// Defines a load/store interface to memory
    Memory { bases: Vec<Param>, pos: TokenStream },
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
    None,
}

/// Defines a field in the interface
///
/// A field may represent a 8, 16, 32, 64 bit region in the state with a
/// specific bit layout and an additional collection of  actions.
#[derive(PartialEq, Clone)]
pub struct InterfaceField {
    // The field itself
    pub field: Field,
    // The ReadAction for this field
    pub readaction: Option<Action>,
    // The WriteAction for this field,
    pub writeaction: Option<Action>,
}

/// Defines an action that is executed on the interface
///
/// An action defines a read access to the state or a write access to the state. The latter
/// basically triggers a state transition.
///
/// Currently an action is basically an assignment that assigns the destination the value of the
/// source. If the destination is a StateRef, then this
///   src => dst
#[derive(PartialEq, Clone)]
pub struct ActionComponent {
    /// the source operand of the action
    pub src: Expr,
    /// the destination operand of the action
    pub dst: Expr,
    /// the location where the action was defined
    pub pos: TokenStream,
}

/// Represents the type of action
///
/// Currently the only supported action types are Read and Write but, we can imagine needing more
/// types to support custom instructions needing to be executed to dump state to memory.
#[derive(PartialEq, Clone)]
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
#[derive(PartialEq, Clone)]
pub struct Action {
    /// the type of the action (Read/Write)
    pub action_type: ActionType,
    /// the list of action components that are associated with this action
    pub action_components: Vec<ActionComponent>,
    /// the location where the action was defined
    pub pos: TokenStream,
}
