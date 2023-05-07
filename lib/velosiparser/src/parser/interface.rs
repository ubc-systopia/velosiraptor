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

//! Interface Parser
//!
//! Software will interact with the interface to query and change the state of the
//! translation unit.
//! Conceptually, there are two operations on the interface: read and write.
//! Each operation then maps to a sequence of actions on the state.

// the used NOM components
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
};

/// library internal includes
use crate::error::IResult;
use crate::parser::{expr::expr, param::parameter, terminals::*};
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeIdentifier, VelosiParseTreeInterface,
    VelosiParseTreeInterfaceAction, VelosiParseTreeInterfaceActions, VelosiParseTreeInterfaceDef,
    VelosiParseTreeInterfaceField, VelosiParseTreeInterfaceFieldMemory,
    VelosiParseTreeInterfaceFieldMmio, VelosiParseTreeInterfaceFieldNode,
    VelosiParseTreeInterfaceFieldRegister, VelosiParseTreeParam, VelosiParseTreeUnitNode,
};
use crate::{VelosiOpToken, VelosiTokenKind, VelosiTokenStream};

/// parses a interface definition
///
/// This function parses a unit's interface definition
///
/// # Grammar
///
/// `INTERFACE := KW_INTERFACE ASSIGN (NONE | IFACEDEF) SEMICOLON`
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
pub fn interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    // let mut pos = input.clone();

    // try to match the interface keyword, if there is no match, return.
    let (i1, _) = kw_interface(input)?;

    // We now attempt to parse the different interface types.
    cut(delimited(assign, alt((ifacedef, ifacenone)), semicolon))(i1)
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
fn ifacenone(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_none(input)?;

    pos.span_until_start(&i1);
    let iface = VelosiParseTreeInterface::None(pos);
    Ok((i1, VelosiParseTreeUnitNode::Interface(iface)))
}

/// parses and consumes an interface definition of a unit
///
/// # Grammar
///
/// `IFACEDEF := KW_INTERFACEDEF IFACEPARAMS LBRACE INTERFACEFIELDS RBRACE`
fn ifacedef(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try to barse the InterfaceDef keyword
    let (i1, _) = kw_interfacedef(input)?;
    let (i2, bases) = ifaceparams(i1)?;
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, ifacefield),
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

/// Parses and consumes a interface field definition
///
/// # Grammar
///
/// `IFACEFIELD := MEMORYFIELD | REGISTERFIELD | MMIOFIELD`
pub fn ifacefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    alt((memoryfield, registerfield, mmiofield))(input)
}

/// Parses and consumes a register interface field definition
///
/// # Grammar
///
/// `MMIOFIELD := KW_MMIO LBRAK NUM RBRACK LBRACE SEPLIST(COMMA, IFACEFIELDBODY) RBRACE`
pub fn registerfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // if we have the reg keyword
    let (i1, _) = kw_reg(input)?;

    let (i2, (name, size)) = cut(tuple((ident, delimited(lbrack, num, rbrack))))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list1(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
        nodes
    } else {
        Vec::new()
    };

    let res = VelosiParseTreeInterfaceFieldRegister::new(name, size, nodes, pos);
    Ok((i3, VelosiParseTreeInterfaceField::Register(res)))
}

/// Parses and consumes a memory interface field definition
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

    let (i2, (name, fieldinfo)) = cut(tuple((ident, delimited(lbrack, memfieldinfo, rbrack))))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list1(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
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
/// # Grammar
///
/// `REGISTERFIELD := KW_REG MEMFIELDINFO LBRACE SEPLIST(COMMA, IFACEFIELDBODY) RBRACE`
pub fn mmiofield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // if we have the mmio keyword
    let (i1, _) = kw_mmio(input)?;

    let (i2, (name, fieldinfo)) = cut(tuple((ident, delimited(lbrack, memfieldinfo, rbrack))))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list1(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let nodes = if let Some(nodes) = nodes {
        nodes
    } else {
        Vec::new()
    };

    let (base, offset, size) = fieldinfo;

    let res = VelosiParseTreeInterfaceFieldMmio::new(name, base, offset, size, nodes, pos);
    Ok((i3, VelosiParseTreeInterfaceField::Mmio(res)))
}

type MemFiledInfo = (VelosiParseTreeIdentifier, u64, u64);

/// Parses the state field information
///
/// # Grammar
///
/// `InterfaceFieldINFO := LBRACK IDENT NUM NUM RBRACK`
pub fn memfieldinfo(input: VelosiTokenStream) -> IResult<VelosiTokenStream, MemFiledInfo> {
    tuple((terminated(ident, comma), terminated(num, comma), num))(input)
}

///
///
fn interfacefieldbody(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    alt((layout, readactions, writeactions))(input)
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
fn layout(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let (i1, _) = kw_layout(input)?;

    let (i2, slices) = delimited(
        lbrace,
        terminated(separated_list0(comma, iface_field_slice), opt(comma)),
        cut(rbrace),
    )(i1)?;

    Ok((i2, VelosiParseTreeInterfaceFieldNode::Layout(slices)))
}

/// Pares and consumes a state field slice definition
///
/// # Grammar
///
/// `iface_field_slice := NUM DOTDOT NUM IDENT`
pub fn iface_field_slice(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeFieldSlice> {
    let mut pos = input.clone();

    let (i1, (start, end, name)) = tuple((num, cut(preceded(dotdot, num)), cut(ident)))(input)?;

    pos.span_until_start(&i1);

    Ok((i1, VelosiParseTreeFieldSlice::new(start, end, name, pos)))
}

/// parses the read actions of a field
///
/// The read actions define what effects a read on the interface may have on the
/// state of the translation unit, if at all
///
/// # Grammar
///
/// READACTION := KW_READACTION actions_block ;
///
/// # Results
///
///  * OK:      the parser could successfully recognize the read actions
///  * Error:   the parser could not recognize the readactions definition keyword
///  * Failure: the parser recognized the read actions, but it did not properly parse
///
/// # Examples
///
/// ReadActions = { .. };
///
fn readactions(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let mut pos = input.clone();

    // try parsing the ReadActions keyword
    let (i1, _) = kw_readaction(input)?;

    // now parse the actions block
    let (i2, action_components) = cut(actions_block)(i1)?;

    pos.span_until_start(&i2);
    let actions = VelosiParseTreeInterfaceActions::new(action_components, pos);
    Ok((i2, VelosiParseTreeInterfaceFieldNode::ReadActions(actions)))
}

/// parses the write actions of a field
///
/// The write actions define what effects a write on the interface may have on the
/// state of the translation unit, if at all
///
/// # Grammar
///
/// WRITEACTION := KW_WRITEACTION ACTIONS_BLOCK ;
///
/// # Results
///
///  * OK:      the parser could successfully recognize the write actions
///  * Error:   the parser could not recognize the write actions definition keyword
///  * Failure: the parser recognized the write actions, but it did not properly parse
///
/// # Examples
///
/// WriteActions = { .. };
///
fn writeactions(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceFieldNode> {
    let mut pos = input.clone();

    // try parsing the WriteActions keyword
    let (i1, _) = kw_writeaction(input)?;

    // now parse the actions block
    let (i2, action_components) = cut(actions_block)(i1)?;

    pos.span_until_start(&i2);
    let actions = VelosiParseTreeInterfaceActions::new(action_components, pos);
    Ok((i2, VelosiParseTreeInterfaceFieldNode::WriteActions(actions)))
}

/// parses an action block
///
/// # Grammar
///
/// ACTIONS_BLOCK := LBRACE LIST(semicolon, ACTION_COMPONENT) RBRACE
///
/// # Results
///
///  * OK:      the parser could successfully recognize the action block
///  * Error:   the parser could not recognize the action block definition keyword
///  * Failure: the parser recognized the action block, but it did not properly parse
///
/// # Examples
///
/// WriteActions = { .. };
///
fn actions_block(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeInterfaceAction>> {
    delimited(lbrace, many0(action_component), rbrace)(input)
}

/// parses an action
///
/// # Grammar
///
/// ACTION_COMPONENT := EXPR ACTION_DIRECTION EXPR
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

    let (src, dst) = match arrow {
        VelosiTokenKind::OpToken(VelosiOpToken::LArrow) => (right, left),
        VelosiTokenKind::OpToken(VelosiOpToken::RArrow) => (left, right),
        _ => panic!("unexpected token"),
    };

    pos.span_until_start(&i1);
    Ok((i1, VelosiParseTreeInterfaceAction::new(src, dst, pos)))
}

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn test_action_components() {
    let content = "state.field -> state.field;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();

    assert!(action_component(ts).is_ok());

    let content = "state.field <- state.field;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(action_component(ts).is_ok());

    let content = "0 -> state.field;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(action_component(ts).is_ok());

    let content = "state -> interface;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(action_component(ts).is_ok());

    let content = "state.field[0..7] -> interface.field[8..15];";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    assert!(action_component(ts).is_ok());
}
