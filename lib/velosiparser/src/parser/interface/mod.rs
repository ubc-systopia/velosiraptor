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
    branch::alt,
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, tuple},
};

// used crate components
use crate::error::IResult;
use crate::parser::{param::parameter, terminals::*};
use crate::parsetree::{
    VelosiParseTreeInterface, VelosiParseTreeInterfaceDef, VelosiParseTreeParam,
    VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

// sub modules
mod actions;
mod field;
mod layout;

/// parses a interface definition
///
/// This function parses a unit's interface definition.
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
/// `INTERFACE := KW_INTERFACE ASSIGN (NONE | IFACEDEF) SEMICOLON`
///
/// # Examples
///
/// * `interface = None;`
///
pub fn interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    // let mut pos = input.clone();

    // try to match the interface keyword, if there is no match, return.
    let (i1, _) = kw_interface(input)?;

    // We now attempt to parse the different interface types.
    cut(delimited(assign, alt((ifacedef, ifacenone)), semicolon))(i1)
}

/// parses the none interface definition
///
/// This represents an empty or non-existent interface definition.
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized none interface as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `NONE_INTERFACE := KW_NONE`
///
/// # Examples
///
/// * `None`
///
fn ifacenone(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_none(input)?;

    pos.span_until_start(&i1);
    let iface = VelosiParseTreeInterface::None(pos);
    Ok((i1, VelosiParseTreeUnitNode::Interface(iface)))
}

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
/// `IFACEDEF := KW_INTERFACEDEF IFACEPARAMS LBRACE INTERFACEFIELDS RBRACE`
///
/// # Examples
///
/// * `InterfaceDef(base: addr) {}`
///
fn ifacedef(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try to barse the InterfaceDef keyword
    let (i1, _) = kw_interfacedef(input)?;
    let (i2, bases) = ifaceparams(i1)?;
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, field::ifacefield),
        tuple((opt(comma), rbrace)),
    ))(i2)?;

    pos.span_until_start(&i3);

    let st = VelosiParseTreeInterfaceDef::new(bases, fields, pos);
    Ok((
        i3,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::InterfaceDef(st)),
    ))
}

/// Parses and consumes a comma separated list of identifiers of the form "(ident, ..., ident)"
///
/// # GRAMMAR
///
/// `IFACEPARAMS := LPAREN SEPLIST(COMMA, PARAMETER) RPAREN
pub fn ifaceparams(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    let (i, p) = opt(delimited(
        lparen,
        cut(separated_list0(comma, parameter)),
        cut(rparen),
    ))(input)?;
    Ok((i, p.unwrap_or_default()))
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
use std::fs;
#[cfg(test)]
use velosilexer::VelosiLexer;

#[cfg(test)]
use crate::{
    test_parse_and_check_fail, test_parse_and_check_ok, test_parse_and_compare_file_fail,
    test_parse_and_compare_ok,
};

#[test]
fn test_iface_params_ok() {
    // empty
    test_parse_and_check_ok!("()", ifaceparams);
    // one param
    test_parse_and_check_ok!("(base: addr)", ifaceparams);
    // two params
    test_parse_and_check_ok!("(base: addr, base2: addr)", ifaceparams);
}

#[test]
fn test_iface_params_fail() {
    // no type
    test_parse_and_check_fail!("(base)", ifaceparams);
    // no separator
    test_parse_and_check_fail!("(base: addr base2: addr)", ifaceparams);
    // wrong separator
    test_parse_and_check_fail!("(base: addr; base2: addr)", ifaceparams);
}

#[test]
fn test_iface_none_ok() {
    test_parse_and_compare_ok!("None", ifacenone, "  interface = None;\n\n");
}

#[test]
fn test_iface_none_fail() {
    // nothing really...
}

#[test]
fn test_iface_def_ok() {
    test_parse_and_compare_ok!(
        "InterfaceDef(){}",
        ifacedef,
        "  interface = InterfaceDef() {\n  };\n\n"
    );
    test_parse_and_compare_ok!(
        "InterfaceDef(base: foo){}",
        ifacedef,
        "  interface = InterfaceDef(base: foo) {\n  };\n\n"
    );
    // with a register
    test_parse_and_compare_ok!(
        "InterfaceDef(base: foo){ reg foo [ 8 ] }",
        ifacedef,
        "  interface = InterfaceDef(base: foo) {\n    reg foo [ 8 ],\n  };\n\n"
    );
    // trailing comma
    test_parse_and_compare_ok!(
        "InterfaceDef(base: foo){ reg foo [ 8 ], }",
        ifacedef,
        "  interface = InterfaceDef(base: foo) {\n    reg foo [ 8 ],\n  };\n\n"
    );
    // with two registers
    test_parse_and_compare_ok!(
        "InterfaceDef(base: foo){ reg foo [ 8 ], reg foo [ 8 ] }",
        ifacedef,
        "  interface = InterfaceDef(base: foo) {\n    reg foo [ 8 ],\n    reg foo [ 8 ],\n  };\n\n"
    );
}

#[test]
fn test_iface_def_fail() {
    // no separator
    test_parse_and_check_fail!(
        "InterfaceDef(base: foo){ reg foo [ 8 ]\n reg foo [ 8 ] }",
        ifacedef
    );
    // wrong separator
    test_parse_and_check_fail!(
        "InterfaceDef(base: foo){ reg foo [ 8 ]; reg foo [ 8 ] }",
        ifacedef
    );
}

#[test]
fn test_iface_def_fail_error_messages() {
    test_parse_and_compare_file_fail!("interface/interface_00_register_not_separated", ifacedef);
    test_parse_and_compare_file_fail!("interface/interface_01_register_wrong_separator", ifacedef);
}

#[test]
fn test_iface() {
    test_parse_and_compare_ok!("interface = None;", interface, "  interface = None;\n\n");
    test_parse_and_compare_ok!(
        "interface = InterfaceDef(base: foo){};",
        interface,
        "  interface = InterfaceDef(base: foo) {\n  };\n\n"
    );
}
