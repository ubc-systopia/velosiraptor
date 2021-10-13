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
//  interface = TYPE(params) {
//      ident [base, offset, length] {
//          Layout {
//              0 4 ident,
//          };
//          ReadAction {
//              expr <- expr;
//          };
//          WriteAction {
//              expr <- expr;
//              expr -> expr;
//          };
//      };
//  };
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

use crate::ast::interface::{ActionComponent, ActionType, InterfaceField};
use crate::ast::{Action, ActionOp, Field, Interface};
use crate::error::IResult;
use crate::error::VrsError::DoubleDef;
use crate::parser::bitslice::bitslice;
use crate::parser::expression::expr;
use crate::parser::field::field;
use crate::parser::state::argument_parser;
use crate::parser::terminals::{assign, boolean, comma, dot, fatarrow, ident, kw_interface, kw_layout, kw_memory, kw_mmio, kw_none, kw_readaction, kw_state, kw_writeaction, lbrace, lbrack, le, num, rbrace, rbrack, semicolon, kw_register};
use crate::token::{TokenStream, Token};
use nom::branch::{alt, permutation};
use nom::character::streaming::one_of;
use nom::combinator::{cut, opt};
use nom::multi::{many0, many1, separated_list0};
use nom::sequence::{delimited, pair, preceded, terminated};
use std::collections::hash_map::RandomState;

/// Interface definition parsing
// TODO Does not yet include parsing for SpecialRegisters
pub fn interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to match the interface keyword, if there is no match, return.TokenStream
    let (i1, _) = kw_state(_input)?;

    // We now attempt to parse the different interface types.
    cut(delimited(
        assign,
        alt((mmio_interface, memory_interface, register_interface, none_interface)),
        semicolon,
    ))(i1)
}

fn none_interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    let (i1, _) = kw_none(_input)?;

    Ok((i1, Interface::None))
}

fn mmio_interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    let (i1, _) = kw_mmio(_input.clone())?;
    let (i2, bases) = argument_parser(i1)?;
    let (i3, fields) = cut(delimited(lbrack, many0(interfacefield), rbrack))(i2)?;

    let pos = _input.expand_until(&i3);
    Ok((i3, Interface::MMIORegisters { bases, fields, pos }))
}

fn register_interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    let (i1, _) = kw_register(_input.clone())?;
    let (i2, fields) = cut(delimited(lbrack, many0(interfacefield), rbrack))(i1)?;

    let pos = _input.expand_until(&i2);
    Ok((i2, Interface::CPURegisters { fields, pos }))
}

fn memory_interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    let (i1, _) = kw_memory(_input.clone())?;

    // Note that the Memory Interface should allow a direct 1-to-1 so for now we will only support the parsing of
    // interface = Memory;
    // as all other information can be just directly received from the state.
    let pos  = _input.expand_until(&i1);
    Ok((i1, Interface::Memory { pos }))
}

/// Parses an interface field
fn interfacefield(input: TokenStream) -> IResult<TokenStream, InterfaceField> {
    // we first start off with an identifier,
    let (i1, name) = ident(input.clone())?;

    // define a parser for the base-offset: baseoffsetparser = ident, num,
    let baseoffsetparser = pair(terminated(ident, cut(comma)), cut(terminated(num, comma)));

    // recognize the field header: [baseoffsetparser, num]
    let (i2, (stateref, length)) =
        cut(delimited(lbrack, pair(opt(baseoffsetparser), num), rbrack))(i1)?;

    // We now parse an optional Layout, ReadAction, WriteAction

    // define the parser for the bitslices: bitslicesparser = {LIST(bitslice, comma)}
    let bitslicesparser = terminated(
        preceded(
            kw_layout,
            delimited(lbrace, cut(separated_list0(comma, bitslice)), rbrace),
        ),
        semicolon,
    );

    // We now parse the field body of Optional Bitslices, ReadAction, WriteAction
    let (i3, (bitslices, readaction, writeaction)) =
        permutation((opt(bitslicesparser), opt(readaction), opt(writeaction)))(i2)?;

    // if there were bitslices parsed unwrap them, otherwise create an empty vector
    let layout = bitslices.unwrap_or_default();

    // calculate the position of the bitslice
    let pos = input.expand_until(&i3);

    let field = Field {
        name,
        stateref,
        length,
        layout,
        pos,
    };

    Ok((
        i3,
        InterfaceField {
            field,
            readaction,
            writeaction,
        },
    ))
}

fn readaction(input: TokenStream) -> IResult<TokenStream, Action> {
    let (i1, _) = kw_readaction(input.clone())?;
    let (i2, action_components) = terminated(
        delimited(lbrace, separated_list0(semicolon, action_component), rbrace),
        semicolon,
    )(i1)?;
    Ok((
        i2,
        Action {
            action_type: ActionType::Read,
            action_components,
            pos: input.expand_until(&i2),
        },
    ))
}

fn writeaction(input: TokenStream) -> IResult<TokenStream, Action> {
    let (i1, _) = kw_writeaction(input.clone())?;
    let (i2, action_components) = terminated(
        delimited(lbrace, separated_list0(semicolon, action_component), rbrace),
        semicolon,
    )(i1)?;
    Ok((
        i2,
        Action {
            action_type: ActionType::Write,
            action_components,
            pos: input.expand_until(&i2),
        },
    ))
}
fn action_component(_input: TokenStream) -> IResult<TokenStream, ActionComponent> {
    // Parse each of the actionOPs and then the pos

    let (i1, left_aop) = expr(_input.clone())?;
    let (i2, mapping_dir) = alt((mapleft, mapright))(i1)?;
    let (i3, right_aop) = expr(i2)?;

    let pos = _input.expand_until(&i3);

    // Order the
    match mapping_dir {
        MappingDirection::LeftToRight => Ok((
            i3,
            ActionComponent {
                src: left_aop,
                dst: right_aop,
                pos,
            },
        )),
        MappingDirection::RightToLeft => Ok((
            i3,
            ActionComponent {
                src: right_aop,
                dst: left_aop,
                pos,
            },
        )),
        MappingDirection::BiDirectional => {
            todo!();
        }
    }
}
/// Expands on the terminal parsers by defining a function with $name that calls $parser and on
/// a success returns the $return_value of type $return_type
macro_rules! terminalparse_with_return_type (
    ($name: ident, $parser: ident, $return_value: expr, $return_type: ty) => (
        fn $name(input: TokenStream) -> IResult<TokenStream, $return_type> {
            match cut($parser)(input) {
                Ok((i1, _)) => {
                    Ok((i1, $return_value))
                }
                Err(x) => Err(x)
            }
        }
    )
);

terminalparse_with_return_type!(readaction_type, kw_readaction, ActionType::Read, ActionType);
terminalparse_with_return_type!(
    writeaction_type,
    kw_writeaction,
    ActionType::Write,
    ActionType
);
terminalparse_with_return_type!(state_string, kw_state, String::from("state"), String);
terminalparse_with_return_type!(
    interface_string,
    kw_interface,
    String::from("interface"),
    String
);

terminalparse_with_return_type!(
    mapright,
    rarrow,
    MappingDirection::LeftToRight,
    MappingDirection
);
terminalparse_with_return_type!(
    mapleft,
    larrow,
    MappingDirection::RightToLeft,
    MappingDirection
);
terminalparse_with_return_type!(
    mapbidir,
    bidirarrow,
    MappingDirection::BiDirectional,
    MappingDirection
);

enum MappingDirection {
    LeftToRight,
    RightToLeft,
    BiDirectional,
}
