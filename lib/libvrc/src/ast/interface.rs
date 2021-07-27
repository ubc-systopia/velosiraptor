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
    Memory { pos: TokenStream },
    /// Defines a memory-mapped interface to registers
    MMIORegisters { pos: TokenStream },
    /// Defines a load/store interface to CPU registers
    CPURegisters { pos: TokenStream },
    /// Defines a register interface using special instructions
    SpecialRegisters { pos: TokenStream },
    // TODO interface may be a combination: e.g., Memory + MMIORegisters
    //CombinedState {  },
    /// No software interface associated with this translation unit
    None,
}

/// Represents an action operand
///
/// The action operand defines the source and destination of an action
pub enum ActionOp {
    /// reference to a field/slice of the interface
    InterfaceRef(String, String),
    /// reference to a field/slice in the state
    StateRef(String, String),
    /// a constant boolean value
    BoolValue(bool),
    /// a constant integer value
    IntValue(u64),
}

/// Defines an action that is executed on the interface
///
/// An action defines a read access to the state or a write access to the state. The latter
/// basically triggers a state transition.
///
/// Currently an action is basically an assignment that assigns the destination the value of the
/// source. If the destination is a StateRef, then this
///   src => dst
pub struct Action {
    /// the source operand of the action
    pub src: ActionOp,
    /// the destination operand of the action
    pub dst: ActionOp,
    /// the location where the action was defined
    pub pos: TokenStream,
}
