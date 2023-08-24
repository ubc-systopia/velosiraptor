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

//! # VelosiParser -- Interface Actions Parsing
//!
//! Interface actions define the effects of reading/writing a field of the interface.
//! It captures how the state of the translation unit changes when a field is read or written.

// used external dependencies
use nom::{
    branch::alt,
    combinator::cut,
    multi::many0,
    sequence::{delimited, preceded, terminated, tuple},
};

// used crate dependencies
use crate::error::IResult;
use crate::parser::{expr::expr, terminals::*};
use crate::parsetree::{
    VelosiParseTreeInterfaceAction, VelosiParseTreeInterfaceActions,
    VelosiParseTreeInterfaceFieldNode,
};
use crate::{VelosiOpToken, VelosiTokenKind, VelosiTokenStream};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Actions Parsing
////////////////////////////////////////////////////////////////////////////////////////////////////

/// parses the read actions of a field
///
/// The read actions define what effects a read on the interface may have on the
/// state of the translation unit, if at all
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized read actions as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `READACTION := KW_READACTION ACTIONS_BLOCK`
///
/// # Examples
///
///  * `ReadActions { interface.field <- state.field; }`
///
pub fn readactions(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let mut pos = input.clone();

    let (i1, action_components) = preceded(kw_readaction, cut(actions_block))(input)?;

    pos.span_until_start(&i1);
    let actions = VelosiParseTreeInterfaceActions::new(action_components, pos);
    Ok((i1, VelosiParseTreeInterfaceFieldNode::ReadActions(actions)))
}

/// parses the write actions of a field
///
/// The write actions define what effects a write on the interface may have on the
/// state of the translation unit, if at all
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized write actions as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `WRITEACTION := KW_WRITEACTION ACTIONS_BLOCK`
///
/// # Examples
///
/// * `WriteActions { interface.field -> state.field; }`
///
pub fn writeactions(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let mut pos = input.clone();

    let (i1, action_components) = preceded(kw_writeaction, cut(actions_block))(input)?;

    pos.span_until_start(&i1);
    let actions = VelosiParseTreeInterfaceActions::new(action_components, pos);
    Ok((i1, VelosiParseTreeInterfaceFieldNode::WriteActions(actions)))
}

/// parses an action block of a read or write action
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized action block as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `ACTIONS_BLOCK := LBRACE ACTION_COMPONENT* RBRACE`
///
/// # Examples
///
/// * `{ interface.field -> state.field; }`
///
fn actions_block(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeInterfaceAction>> {
    delimited(lbrace, many0(action_component), rbrace)(input)
}

/// parses a single action component
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized action component as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `ACTION_COMPONENT := EXPR [ LARROW | RARROW ] EXPR`
///
/// # Results
///
///  * OK:      the parser could successfully recognize the action
///  * Error:   the parser could not recognize the action definition keyword
///  * Failure: the parser recognized the action, but it did not properly parse
///
/// # Examples
///
/// WriteActions = { .. };
///
fn action_component(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceAction> {
    let mut pos = input.clone();

    // Parse each of the action ops
    let arrows = alt((larrow, rarrow));

    // parse the <expr> OP <expr> scheme, and match on the token
    let (i1, (left, arrow, right)) =
        terminated(tuple((expr, cut(arrows), cut(expr))), cut(semicolon))(input)?;

    // make sure we have the right src -> dst order
    let (src, dst) = match arrow {
        VelosiTokenKind::OpToken(VelosiOpToken::LArrow) => (right, left),
        VelosiTokenKind::OpToken(VelosiOpToken::RArrow) => (left, right),
        _ => unreachable!("BUG: parsed something else than an arrow!"),
    };

    pos.span_until_start(&i1);
    Ok((i1, VelosiParseTreeInterfaceAction::new(src, dst, pos)))
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
    test_parse_and_check_fail, test_parse_and_compare_file_fail, test_parse_and_compare_ok,
};

#[test]
fn test_action_components_ok() {
    // standard behavior
    test_parse_and_compare_ok!("interface.field -> state.field;", action_component);
    test_parse_and_compare_ok!(
        "interface.field <- state.field;",
        action_component,
        "state.field -> interface.field;"
    );
    test_parse_and_compare_ok!(
        "state.field[0..7] -> interface.field[8..15];",
        action_component
    );

    // assigning constants
    test_parse_and_compare_ok!("0 -> state.field;", action_component);
    test_parse_and_compare_ok!("0 + 2 -> state.field;", action_component);

    // expressions
    test_parse_and_compare_ok!("interface.field + 2 -> state.field;", action_component);
    test_parse_and_compare_ok!(
        "interface.field <- state.field + 2;",
        action_component,
        "state.field + 2 -> interface.field;"
    );

    // this still should parse fine
    test_parse_and_compare_ok!("state.field -> state.field;", action_component);
    test_parse_and_compare_ok!(
        "interface.field <- interface.field;",
        action_component,
        "interface.field -> interface.field;"
    );

    // doesn't make much sense, but should still parse fine
    test_parse_and_compare_ok!("0 <- state.field;", action_component, "state.field -> 0;");
    test_parse_and_compare_ok!("state.field -> 0;", action_component);
    test_parse_and_compare_ok!("1 -> 0;", action_component);
    test_parse_and_compare_ok!("0 -> var;", action_component);
    test_parse_and_compare_ok!("var -> CONST;", action_component);
}

#[test]
fn test_action_components_fail() {
    // missing semicolon
    test_parse_and_check_fail!("0 -> state.field", action_component);
    // wrong kind of arrows
    test_parse_and_check_fail!("0 => state.field", action_component);
    test_parse_and_check_fail!("0 <= state.field", action_component);
    test_parse_and_check_fail!("0 = state.field", action_component);
    test_parse_and_check_fail!("0 ==> state.field", action_component);
}

#[test]
fn test_read_actions_ok() {
    // empty
    test_parse_and_compare_ok!("ReadActions { }", readactions, "ReadActions {\n}");
    // single
    test_parse_and_compare_ok!(
        "ReadActions { A -> B; }",
        readactions,
        "ReadActions {\n  A -> B;\n}"
    );
    test_parse_and_compare_ok!(
        "ReadActions { A -> B; A -> B; }",
        readactions,
        "ReadActions {\n  A -> B;\n  A -> B;\n}"
    );
}

#[test]
fn test_read_actions_fail() {
    // missing semicolon
    test_parse_and_check_fail!("ReadActions { A -> B }", readactions);
    // wrong separator
    test_parse_and_check_fail!("ReadActions { A -> B, }", readactions);
    // nop separator
    test_parse_and_check_fail!("ReadActions { A -> B A -> B; }", readactions);
    // wrong separator
    test_parse_and_check_fail!("ReadActions { A -> B,  A -> B; }", readactions);
}

#[test]
fn test_read_actions_fail_error_msg() {
    // testing the error output
    test_parse_and_compare_file_fail!(
        "interface/parts/readactions_00_missing_semicolon",
        readactions
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/readactions_01_missing_separator",
        readactions
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/readactions_02_wrong_separator",
        readactions
    );
}

#[test]
fn test_write_actions_ok() {
    // empty
    test_parse_and_compare_ok!("WriteActions { }", writeactions, "WriteActions {\n}");
    // single
    test_parse_and_compare_ok!(
        "WriteActions { A -> B; }",
        writeactions,
        "WriteActions {\n  A -> B;\n}"
    );
    test_parse_and_compare_ok!(
        "WriteActions { A -> B; A -> B; }",
        writeactions,
        "WriteActions {\n  A -> B;\n  A -> B;\n}"
    );
}

#[test]
fn test_write_actions_fail() {
    // missing semicolon
    test_parse_and_check_fail!("WriteActions { A -> B }", writeactions);
    // wrong separator
    test_parse_and_check_fail!("WriteActions { A -> B, }", writeactions);
    // nop separator
    test_parse_and_check_fail!("WriteActions { A -> B A -> B; }", writeactions);
    // wrong separator
    test_parse_and_check_fail!("WriteActions { A -> B,  A -> B; }", writeactions);
}

#[test]
fn test_write_actions_fail_error_msg() {
    // testing the error output
    test_parse_and_compare_file_fail!(
        "interface/parts/writeactions_00_missing_semicolon",
        writeactions
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/writeactions_01_missing_separator",
        writeactions
    );
    test_parse_and_compare_file_fail!(
        "interface/parts/writeactions_02_wrong_separator",
        writeactions
    );
}
