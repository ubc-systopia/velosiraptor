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

// the used NOM components
use nom::{
    branch::{alt, permutation},
    combinator::{cut, opt},
    multi::{many1, separated_list0},
    sequence::{delimited, preceded, terminated},
    Err,
};

/// library internal includes
use crate::ast::{Action, ActionComponent, ActionType, BitSlice, Field, Interface, InterfaceField};
use crate::error::IResult;
use crate::parser::{
    bitslice::bitslice_block, expression::expr, field::field_params, state::argument_parser,
    terminals::*,
};
use crate::token::TokenStream;

/// parses a interface definition
///
/// This function parses a unit's interface definition
///
/// # Grammar
///
/// INTERFACE_DEFS := NONE_INTERFACE | MMIO_INTERFACE | MEMORY_INTERFACE | REGISTER_INTERFACE
/// INTERFACE := KW_INTERFACE = INTERFACE_DEFS ;
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface
///  * Error:   the parser could not recognize the interface definition keyword
///  * Failure: the parser recognized the interface, but it did not properly parse
///
/// # Examples
///
/// interface = None;
///
pub fn interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to match the interface keyword, if there is no match, return.
    let (i1, _) = kw_interface(input)?;

    // We now attempt to parse the different interface types.
    cut(delimited(
        assign,
        alt((
            mmio_interface,
            memory_interface,
            register_interface,
            none_interface,
        )),
        semicolon,
    ))(i1)
}

/// parses the none interface definition
///
/// # Grammar
///
/// NONE_INTERFACE := KW_NONE
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface
///  * Error:   the parser could not recognize the interface definition keyword
///
/// # Examples
///
/// None
///
fn none_interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try parse the none keyword and return
    let (i1, _) = kw_none(input)?;
    Ok((i1, Interface::None))
}

/// parses the mmio interface definition
///
/// This interface is a register-like, memory-mapped interface. Software uses loads and
/// stores to interoperate with the interface. In contrast to the memory interface,
/// the MMIO interface may:
///   - Hide parts of the state from software
///   - trigger multiple state transitions
///   - Software may need to use a specific load/store instructions (e.g., non-cached)
///
/// # Grammar
///
/// MMIO_INTERFACE := KW_MMIO LPAREN PARAMS RPAREN LBRACK (INTERFACEFIELD)+ RBRACK
///
/// # Results
///
///  * OK:      the parser could successfully recognize the mmio interface
///  * Error:   the parser could not recognize the mmio interface definition keyword
///  * Failure: the parser recognized the mmion interface, but it did not properly parse
///
/// # Examples
///
/// MMIOInterface(base : addr) { ... }
///
fn mmio_interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to barse the MMIO keyword
    let (i1, _) = kw_mmio(input.clone())?;

    // try to parse the arguments, must succeed
    let (i2, bases) = cut(argument_parser)(i1)?;

    // next try to parse the interface field definitions
    let (i3, fields) = cut(delimited(lbrack, many1(interfacefield), rbrack))(i2)?;

    // get the new position, and construct ast node
    let pos = input.expand_until(&i3);
    Ok((i3, Interface::MMIORegisters { bases, fields, pos }))
}

/// parses the cpu register interface definition
///
/// This interface is a non-memory-mapped register interface. Software uses loads/stores
/// to register locations rather than memory addresses.
///
/// The interface may
///   - Hide parts of the state from software
///   - trigger multiple state transitions
///   - Software uses registers ad destination
///
/// # Grammar
///
/// REGISTER_INTERFACE := KW_REGISTER LPAREN PARAMS RPAREN LBRACK (INTERFACEFIELD)+ RBRACK
///
/// # Results
///
///  * OK:      the parser could successfully recognize the mmio interface
///  * Error:   the parser could not recognize the mmio interface definition keyword
///  * Failure: the parser recognized the register interface, but it did not properly parse
///
/// # Examples
///
/// MMIOInterface(base : addr) {}
///
fn register_interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try parse the registe rkeyword or return
    let (i1, _) = kw_register(input.clone())?;

    // try to parse the arguments, must succeed
    let (i2, _bases) = cut(argument_parser)(i1)?;

    // now parse the interface fields
    let (i3, fields) = cut(delimited(lbrack, many1(interfacefield), rbrack))(i2)?;

    // get the new position, and construct ast node
    let pos = input.expand_until(&i3);
    Ok((i3, Interface::CPURegisters { fields, pos }))
}

/// parses the memory interface definition
///
/// This interface is a memory-backed interface. Software uses load/store to normal memory
/// locationst to
///
/// The interface may
///   - Hide parts of the state from software
///   - trigger multiple state transitions
///   - Software uses registers ad destination
///
/// # Grammar
///
/// MMIO_INTERFACE := KW_MEMORY [ LPAREN PARAMS RPAREN LBRACK (INTERFACEFIELD)+ RBRACK  ]
///
/// # Results
///
///  * OK:      the parser could successfully recognize the memory interface
///  * Error:   the parser could not recognize the memory interface definition keyword
///  * Failure: the parser recognized the memory interface, but it did not properly parse
///
/// # Examples
///
/// MemoryInterface(base : addr) {}
///
fn memory_interface(_input: TokenStream) -> IResult<TokenStream, Interface> {
    // try parse the memory keyword, or return
    let (i1, _) = kw_memory(_input.clone())?;

    // if the memory interface is a true identity, then we're done here, otherwise we are
    // constructing an normal interface definition with fields
    let (i2, (bases, fields)) = match argument_parser(i1.clone()) {
        Ok((i, bases)) => {
            let (i3, fields) = cut(delimited(lbrack, many1(interfacefield), rbrack))(i)?;
            (i3, (bases, fields))
        }
        Err(Err::Error(_)) => (i1, (Vec::new(), Vec::new())),
        Err(x) => return Err(x),
    };

    // get the new position, and construct ast node
    let pos = _input.expand_until(&i2);
    Ok((i2, Interface::Memory { bases, fields, pos }))
}

/// parses a single interface field definition
///
/// The interface field gives a name to a specific portion of the software-visible
/// interface. It contains:
///   - Layout: the meaning of the bits in the field
///   - ReadAction: what happens when a read operation is carried out on the field
///   - WriteAction: what happens when a write operation is carried out on the field
///
/// # Grammar
///
/// INTERFACE_FIELD := IDENT FIELD_PARAMS (LAYOUT, READACTION, WRITEACTION)
///
/// # Results
///
///  * OK:      the parser could successfully recognize the interface field
///  * Error:   the parser could not recognize  the interface field definition keyword
///  * Failure: the parser recognized the interface field, but it did not properly parse
///
/// # Examples
///
/// foo [base, 0, 0] {...}
///
fn interfacefield(input: TokenStream) -> IResult<TokenStream, InterfaceField> {
    // we first start off with an identifier, no cut here
    let (i1, name) = ident(input.clone())?;

    // recognize the field params
    let (i2, (stateref, length)) = cut(field_params)(i1)?;

    // We now parse an optional Layout, ReadAction, WriteAction
    let (i3, (bitslices, readaction, writeaction)) =
        permutation((opt(layout), opt(readaction), opt(writeaction)))(i2)?;

    // if there were bitslices parsed unwrap them, otherwise create an empty vector
    let layout = bitslices.unwrap_or_default();

    // calculate the position of the bitslice
    let pos = input.expand_until(&i3);

    // assemble the field definition
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

/// parses the layout of an interface filed
///
/// # Grammar
///
/// LAYOUT := KW_LAYOUT BITSLICE_BLOCK ;
///
/// # Results
///
///  * OK:      the parser could successfully recognize the layout
///  * Error:   the parser could not recognize  the layout definition keyword
///  * Failure: the parser recognized the layout, but it did not properly parse
///
/// # Examples
///
/// layout = { .. }
///
fn layout(input: TokenStream) -> IResult<TokenStream, Vec<BitSlice>> {
    terminated(preceded(kw_layout, cut(bitslice_block)), cut(semicolon))(input)
}

fn readaction(input: TokenStream) -> IResult<TokenStream, Action> {
    let (i1, _) = kw_readaction(input.clone())?;
    let (i2, action_components) = terminated(
        delimited(lbrace, separated_list0(semicolon, action_component), rbrace),
        semicolon,
    )(i1)?;
    let pos = input.expand_until(&i2);
    Ok((
        i2,
        Action {
            action_type: ActionType::Read,
            action_components,
            pos,
        },
    ))
}

fn writeaction(input: TokenStream) -> IResult<TokenStream, Action> {
    let (i1, _) = kw_writeaction(input.clone())?;
    let (i2, action_components) = terminated(
        delimited(lbrace, separated_list0(semicolon, action_component), rbrace),
        semicolon,
    )(i1)?;
    let pos = input.expand_until(&i2);
    Ok((
        i2,
        Action {
            action_type: ActionType::Write,
            action_components,
            pos,
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
