// VelosiParser -- Parser for the VelosiRaptor specification language
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

//! # VelosiParser -- Interface Parser
//!
//! Software will interact with the interface to query and change the state of the translation unit.
//! Conceptually, there are two operations on the interface: read and write.
//! Each operation then maps to a sequence of actions on the state.

// used external dependencies
use nom::{
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, tuple},
};

// used crate components
use crate::error::IResult;
use crate::parser::{parameter::param_list, terminals::*};
use crate::parsetree::VelosiParseTreeInterface;
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

// sub modules
mod actions;
mod field;
mod layout;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses and consumes an interface definition of a unit
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized interface definition as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `INTERFACE := KW_INTERFACE IFACEPARAMS LBRACE INTERFACEFIELDS RBRACE`
///
/// # Examples
///
/// * `interface(base: addr) {}`
///
pub fn interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeInterface> {
    let mut pos = input.clone();

    // try to barse the interface keyword
    let (i1, _) = kw_interface(input)?;
    let (i2, bases) = param_list(i1)?;
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, field::ifacefield),
        tuple((opt(comma), rbrace)),
    ))(i2)?;

    pos.span_until_start(&i3);

    Ok((i3, VelosiParseTreeInterface::new(bases, fields, pos)))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{test_parse_and_check_fail, test_parse_and_compare_ok};

#[test]
fn test_iface_def_ok() {
    test_parse_and_compare_ok!("interface(){}", interface, "interface() {\n}");
    test_parse_and_compare_ok!(
        "interface(base: foo){}",
        interface,
        "interface(base: foo) {\n}"
    );
    // with a register
    test_parse_and_compare_ok!(
        "interface(base: foo){ reg foo [ 8 ] }",
        interface,
        "interface(base: foo) {\n  reg foo [ 8 ],\n}"
    );
    // trailing comma
    test_parse_and_compare_ok!(
        "interface(base: foo){ reg foo [ 8 ], }",
        interface,
        "interface(base: foo) {\n  reg foo [ 8 ],\n}"
    );
    // with two registers
    test_parse_and_compare_ok!(
        "interface(base: foo){ reg foo [ 8 ], reg foo [ 8 ] }",
        interface,
        "interface(base: foo) {\n  reg foo [ 8 ],\n  reg foo [ 8 ],\n}"
    );
}

#[test]
fn test_iface_def_fail() {
    // no separator
    test_parse_and_check_fail!(
        "interface(base: foo){ reg foo [ 8 ]\n reg foo [ 8 ] }",
        interface
    );
    // wrong separator
    test_parse_and_check_fail!(
        "interface(base: foo){ reg foo [ 8 ]; reg foo [ 8 ] }",
        interface
    );
}

// #[test]
// fn test_iface_def_fail_error_messages() {
//     test_parse_and_compare_file_fail!("interface/parts/interface_00_register_not_separated", interface);
//     test_parse_and_compare_file_fail!("interface/parts/interface_01_register_wrong_separator", interface);
// }
