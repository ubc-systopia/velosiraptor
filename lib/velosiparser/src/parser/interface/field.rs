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

//! # VelosiParser -- Interface Fields
//!
//! The Interface field parser recognizes definitions of memory, register and mmio fields
//! of the interface.

// used external dependencies
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::separated_list0,
    sequence::{delimited, terminated, tuple},
    Err,
};

use super::actions;
use super::layout;
use crate::error::{IResult, VelosiParserErrBuilder};
/// library internal includes
use crate::parser::terminals::*;
use crate::parsetree::{
    VelosiParseTreeIdentifier, VelosiParseTreeInterfaceField, VelosiParseTreeInterfaceFieldMemory,
    VelosiParseTreeInterfaceFieldMmio, VelosiParseTreeInterfaceFieldNode,
    VelosiParseTreeInterfaceFieldRegister,
};
use crate::{VelosiParserErr, VelosiTokenStream};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Actions Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Parses an interface field definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized interface field as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `IFACEFIELD := MEMORYFIELD | REGISTERFIELD | MMIOFIELD`
///
pub fn ifacefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    alt((memoryfield, registerfield, mmiofield))(input)
}

/// Parses and consumes a register interface field definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized register field as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `MMIOFIELD := KW_MMIO LBRAK NUM RBRACK LBRACE SEPLIST(COMMA, IFACEFIELDBODY) RBRACE`
///
pub fn registerfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // if we have the reg keyword
    let (i1, _) = kw_reg(input)?;

    let (i2, (name, size)) = cut(tuple((ident, delimited(lbrack, num, rbrack))))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
        if nodes.is_empty() {
            return Err(empty_field_err(i3));
        }
        nodes
    } else {
        Vec::new()
    };

    let res = VelosiParseTreeInterfaceFieldRegister::new(name, size, nodes, pos);
    Ok((i3, VelosiParseTreeInterfaceField::Register(res)))
}

/// Parses and consumes a memory interface field definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized memory field as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `MEMORYFIELD := KW_MEM MEMFIELDINFO LBRACE SEPLIST(COMMA, IFACEFIELDBODY) RBRACE`
pub fn memoryfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // if we have the memory keyword
    let (i1, _) = kw_mem(input)?;

    let (i2, (name, fieldinfo)) = tuple((
        cut(ident),
        delimited(cut(lbrack), memfieldinfo, cut(rbrack)),
    ))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
        if nodes.is_empty() {
            return Err(empty_field_err(i3));
        }
        nodes
    } else {
        Vec::new()
    };

    let (base, offset, size) = fieldinfo;

    let res = VelosiParseTreeInterfaceFieldMemory::new(name, base, offset, size, nodes, pos);
    Ok((i3, VelosiParseTreeInterfaceField::Memory(res)))
}

/// Parses and consumes a mmio interface field definition
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized mmio field as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `REGISTERFIELD := KW_REG MEMFIELDINFO LBRACE SEPLIST(COMMA, IFACEFIELDBODY) RBRACE`
pub fn mmiofield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // if we have the mmio keyword
    let (i1, _) = kw_mmio(input)?;

    let (i2, (name, fieldinfo)) = tuple((
        cut(ident),
        delimited(cut(lbrack), memfieldinfo, cut(rbrack)),
    ))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
        if nodes.is_empty() {
            return Err(empty_field_err(i3));
        }
        nodes
    } else {
        Vec::new()
    };

    let (base, offset, size) = fieldinfo;

    let res = VelosiParseTreeInterfaceFieldMmio::new(name, base, offset, size, nodes, pos);
    Ok((i3, VelosiParseTreeInterfaceField::Mmio(res)))
}

fn empty_field_err(loc: VelosiTokenStream) -> Err<VelosiParserErr> {
    let errmsg = "empty interface field block";
    let hint = "remove the block or fill it in explicitly";
    let err = VelosiParserErrBuilder::new(errmsg.to_string())
        .add_tokstream(loc)
        .add_hint(hint.to_string())
        .build();
    Err::Failure(err)
}

type MemFiledInfo = (VelosiParseTreeIdentifier, u64, u64);

/// Parses a memory field information block (base, offset, size)
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized mmio field as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
/// # Grammar
///
/// `InterfaceFieldINFO := LBRACK IDENT NUM NUM RBRACK`
pub fn memfieldinfo(input: VelosiTokenStream) -> IResult<VelosiTokenStream, MemFiledInfo> {
    tuple((
        terminated(cut(ident), cut(comma)),
        terminated(cut(num), cut(comma)),
        cut(num),
    ))(input)
}

/// parses the body of a field definition (layout, read and write actions)
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized field body as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///             and that another parser would fail.
///
fn interfacefieldbody(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    alt((layout::layout, actions::readactions, actions::writeactions))(input)
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
fn test_memfieldinfo_ok() {
    test_parse_and_check_ok!("base, 8, 8", memfieldinfo);
}

#[test]
fn test_memfieldinfo_fail() {
    // empty field definition
    test_parse_and_check_fail!("8", memfieldinfo);
    test_parse_and_check_fail!("base, 8", memfieldinfo);
    test_parse_and_check_fail!("base 8 8", memfieldinfo);
    test_parse_and_check_fail!("base 8 a", memfieldinfo);
}

#[test]
fn test_register_field_ok() {
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { Layout {} }",
        registerfield,
        "    reg foo [ 8 ] {\n      Layout {\n      },\n    }"
    );
    // trailing comma is ok
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { Layout {}, }",
        registerfield,
        "    reg foo [ 8 ] {\n      Layout {\n      },\n    }"
    );
    // it's ok to have the elements twice
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { Layout {}, Layout {}, }",
        registerfield,
        "    reg foo [ 8 ] {\n      Layout {\n      },\n      Layout {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { WriteActions {}, WriteActions {}, }",
        registerfield,
        "    reg foo [ 8 ] {\n      WriteActions {\n      },\n      WriteActions {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { ReadActions {}, ReadActions {}, }",
        registerfield,
        "    reg foo [ 8 ] {\n      ReadActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    // different orders of the body elements are ok
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { Layout {}, WriteActions{}, ReadActions{} }",
        registerfield,
        "    reg foo [ 8 ] {\n      Layout {\n      },\n      WriteActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { ReadActions {}, Layout {}, WriteActions{}, }",
        registerfield,
        "    reg foo [ 8 ] {\n      ReadActions {\n      },\n      Layout {\n      },\n      WriteActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "reg foo [ 8 ] { WriteActions {}, Layout {}, ReadActions{} }",
        registerfield,
        "    reg foo [ 8 ] {\n      WriteActions {\n      },\n      Layout {\n      },\n      ReadActions {\n      },\n    }"
    );
}

#[test]
fn test_register_field_fail() {
    // empty field definition
    test_parse_and_check_fail!("reg foo [ 8 ] {}", registerfield);

    // memory field information instead of register field information
    test_parse_and_check_fail!("reg foo [ base, 8, 8] {Layout {}}", registerfield);
    test_parse_and_check_fail!("reg foo [ base, 8, 8] {Layout {}}", registerfield);
}

#[test]
fn test_register_field_fail_error_messages() {
    // empty field definition
    test_parse_and_compare_file_fail!("interface/parts/registerfield_00_empty_body", registerfield);

    // memory field information instead of register field information
    test_parse_and_compare_file_fail!(
        "interface/parts/registerfield_01_field_info_wrong",
        registerfield
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/registerfield_02_field_info_wrong_2",
        registerfield
    );
}

#[test]
fn test_memory_field_ok() {
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ]",
        memoryfield,
        "    mem foo [ base, 0, 8 ]"
    );

    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { Layout {} }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      Layout {\n      },\n    }"
    );
    // trailing comma is ok
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { Layout {}, }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      Layout {\n      },\n    }"
    );
    // it's ok to have the elements twice
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { Layout {}, Layout {}, }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      Layout {\n      },\n      Layout {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { WriteActions {}, WriteActions {}, }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      WriteActions {\n      },\n      WriteActions {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { ReadActions {}, ReadActions {}, }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      ReadActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    // different orders of the body elements are ok
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { Layout {}, WriteActions{}, ReadActions{} }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      Layout {\n      },\n      WriteActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { ReadActions {}, Layout {}, WriteActions{}, }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      ReadActions {\n      },\n      Layout {\n      },\n      WriteActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "mem foo [ base, 0, 8 ] { WriteActions {}, Layout {}, ReadActions{} }",
        memoryfield,
        "    mem foo [ base, 0, 8 ] {\n      WriteActions {\n      },\n      Layout {\n      },\n      ReadActions {\n      },\n    }"
    );
}

#[test]
fn test_memory_field_fail() {
    // empty field definition
    test_parse_and_check_fail!("mem foo [ base, 0, 8 ] {}", memoryfield);

    // register field information instead of memory field information
    test_parse_and_check_fail!("mem foo [ 8 ] {Layout {}}", memoryfield);
    test_parse_and_check_fail!("mem foo [ base, 8 ] {Layout {}}", memoryfield);
    test_parse_and_check_fail!("mem foo [ base 8 0 ] {Layout {}}", memoryfield);
}

#[test]
fn test_memory_field_fail_error_messages() {
    // empty field definition
    test_parse_and_compare_file_fail!("interface/parts/memoryfield_00_empty_body", memoryfield);

    // memory field information instead of register field information
    test_parse_and_compare_file_fail!(
        "interface/parts/memoryfield_01_field_info_wrong",
        memoryfield
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/memoryfield_02_field_info_wrong_2",
        memoryfield
    );
}

#[test]
fn test_mmio_field_ok() {
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ]",
        mmiofield,
        "    mmio foo [ base, 0, 8 ]"
    );

    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { Layout {} }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      Layout {\n      },\n    }"
    );
    // trailing comma is ok
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { Layout {}, }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      Layout {\n      },\n    }"
    );
    // it's ok to have the elements twice
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { Layout {}, Layout {}, }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      Layout {\n      },\n      Layout {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { WriteActions {}, WriteActions {}, }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      WriteActions {\n      },\n      WriteActions {\n      },\n    }"
    );

    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { ReadActions {}, ReadActions {}, }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      ReadActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    // different orders of the body elements are ok
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { Layout {}, WriteActions{}, ReadActions{} }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      Layout {\n      },\n      WriteActions {\n      },\n      ReadActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { ReadActions {}, Layout {}, WriteActions{}, }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      ReadActions {\n      },\n      Layout {\n      },\n      WriteActions {\n      },\n    }"
    );
    test_parse_and_compare_ok!(
        "mmio foo [ base, 0, 8 ] { WriteActions {}, Layout {}, ReadActions{} }",
        mmiofield,
        "    mmio foo [ base, 0, 8 ] {\n      WriteActions {\n      },\n      Layout {\n      },\n      ReadActions {\n      },\n    }"
    );
}

#[test]
fn test_mmio_field_fail() {
    // empty field definition
    test_parse_and_check_fail!("mmio foo [ base, 0, 8 ] {}", mmiofield);

    // register field information instead of memory field information
    test_parse_and_check_fail!("mmio foo [ 8 ] {Layout {}}", mmiofield);
    test_parse_and_check_fail!("mmio foo [ base, 8 ] {Layout {}}", mmiofield);
    test_parse_and_check_fail!("mmio foo [ base 8 0 ] {Layout {}}", mmiofield);
}

#[test]
fn test_mmio_field_fail_error_messages() {
    // empty field definition
    test_parse_and_compare_file_fail!("interface/parts/mmiofield_00_empty_body", mmiofield);

    // memory field information instead of register field information
    test_parse_and_compare_file_fail!("interface/parts/mmiofield_01_field_info_wrong", mmiofield);
    test_parse_and_compare_file_fail!("interface/parts/mmiofield_02_field_info_wrong_2", mmiofield);
}
