// Velosiraptor Parser
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

//! Interface Parser
//!
//! Software will interact with the interface to query and change the state of the
//! translation unit.
//! Conceptually, there are two operations on the interface: read and write.
//! Each operation then maps to a sequence of actions on the state.

// interface = TYPE(params) {              // the interface as a type
//     ident [base, offset, length] => {   // gives a name to the interface field
//         state.field = 1;                // a list of actions that is performed
//         state.field2 = 2;
//     }
// }
//
// The supported interfaces depend on the used State type.
//
//  * Memory State:   In this state, we assume that all the state is exernal
//                    to the translation unit and thus can be fully accessed
//                    The corresponding interface is roughly an identity map.
//                    Each field has its corresponding field in the interface,
//                    read/writes correspond to a single read/write operation.
//                    The used address might be the same as in the state definition,
//                    or it might be something different.
//                    `interface = Memory(base);`
//
//  * Register State: Only the translation unit has full access to the state,
//                    software will need to go through an exposed interface,
//                    that exposes some of the state directly, none at all
//                    and may contain other registers or alike not direcly
//                    related to the state.
//
//
//  interface = MMIO(base) {
//      ident [base, offset,length] <=> state.field
//  };
//
//  interface = MMIO(base) {      // // mov base, rax ;  mov #2134, (rax)
//      ident [base, offset, length] {
//          0 4  ident <=> state.field[.slice],
//      }
//
//      ident [base, offset, length] {
//          Layout {
//             0 4  ident,
//          }
//         ReadAction {
//             ident <= state.field.slice
//         }
//         WriteAction {
//             ident => state.field.slice
//         }
//      }
//
//      ident [base, offset, length] => None;
//  };
//
//  interface = CPURegs {
//      regname <=> state.regname;
//  }
//
//  interface = CPURegs {
//      reg base [size] => None;        // mov #2134, %base      arch::write_base_reg()
//      reg length [size] => None;
//      reg trigger {                   // mov 1, trigger
//          base => state.base;
//          length => state.length;
//          1 => state.valid;
//          ok <= 1;
//      }
//
//      reg status {
//          base <= state.base;
//          0    => state.valid
//      }
//
//      reg clear {                    // mrs 1, clear
//          0 => state.base;
//          0 => state.length;
//          0 => state.valid;
//      }
//      instr Foo(asdf) {            // foo #1234          arch::foo(1234);
//          state.base = asdf;
//      }
//  }
//
//  TODO: there can be load/stores to specific registers, or simply an instruction executed.
//  TODO: there can be loads and stores that do different things.
//
//
//  * No Interface:   In addition there might be no interface at all
//                    `interface = None;`

use crate::token::TokenStream;
use crate::error::IResult;
use crate::ast::Interface;
use crate::parser::terminals::{kw_interface, assign, semicolon, kw_none};
use nom::combinator::cut;
use nom::branch::alt;
use nom::sequence::delimited;

/// Parses and consumes the [Interface] of a Unit
pub fn interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to match the interface keyword
    let (i1,_) = kw_interface(input)?;
    // We can now parse the different interface types
    cut(delimited(
        assign,
        alt((memory, mmio_registers, cpu_registers, special_registers, none)),
        semicolon
    ))(i1)
}

fn memory(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn mmio_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn cpu_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn special_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

/// Parses and consumes a None interface.
fn none(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to match None keyword
    let (i1,_) = kw_none(input)?;
    Ok((i1, Interface::None))
}

