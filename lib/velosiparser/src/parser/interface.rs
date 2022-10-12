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
    multi::{many0, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};

/// library internal includes
use crate::error::IResult;
use crate::parser::{expr, param::parameter, terminals::*};
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeInterface, VelosiParseTreeInterfaceAction,
    VelosiParseTreeInterfaceActions, VelosiParseTreeInterfaceDef, VelosiParseTreeInterfaceField,
    VelosiParseTreeInterfaceFieldNode, VelosiParseTreeParam, VelosiParseTreeUnitNode,
};
use crate::{VelosiOpToken, VelosiTokenKind, VelosiTokenStream};

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
pub fn interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    // let mut pos = input.clone();

    // try to match the interface keyword, if there is no match, return.
    let (i1, _) = kw_interface(input)?;

    // We now attempt to parse the different interface types.
    cut(delimited(
        assign,
        alt((
            mmio_interface,
            memory_interface,
            cpuregister_interface,
            none_interface,
        )),
        opt(semicolon),
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
fn none_interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_none(input)?;

    pos.span_until_start(&i1);

    Ok((
        i1,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::None(pos)),
    ))
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
/// MMIO_INTERFACE := KW_MMIO LPAREN PARAMS RPAREN LBRACE (INTERFACEFIELD)+ RBRACE
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
fn mmio_interface(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try to barse the MMIO keyword
    let (i1, _) = kw_mmiointerface(input)?;

    // try to parse the arguments, must succeed
    let (i2, bases) = cut(interfaceparams)(i1)?;

    // next try to parse the interface field definitions
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, interfacefield),
        rbrace,
    ))(i2)?;

    pos.span_until_start(&i3);

    let st = VelosiParseTreeInterfaceDef::new(bases, fields, pos);
    Ok((
        i3,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::MMIORegister(st)),
    ))
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
/// REGISTER_INTERFACE := KW_REGISTER LPAREN PARAMS RPAREN LBRACE (INTERFACEFIELD)+ RBRACE
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
fn cpuregister_interface(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try parse the registe rkeyword or return
    let (i1, _) = kw_cpuregisterinterface(input)?;

    // try to parse the arguments, must succeed
    let (i2, bases) = cut(interfaceparams)(i1)?;

    // now parse the interface fields
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, interfacefield),
        rbrace,
    ))(i2)?;

    pos.span_until_start(&i3);

    let st = VelosiParseTreeInterfaceDef::new(bases, fields, pos);
    Ok((
        i3,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::CPURegister(st)),
    ))
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
/// MMIO_INTERFACE := KW_MEMORY LPAREN PARAMS RPAREN LBRACE (INTERFACEFIELD)+ RBRACE
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
fn memory_interface(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    alt((memory_interface_identity, memory_interface_full))(input)
}

fn memory_interface_full(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try parse the registe rkeyword or return
    let (i1, _) = kw_memoryinterface(input)?;

    // try to parse the arguments, must succeed
    let (i2, bases) = cut(interfaceparams)(i1)?;

    // now parse the interface fields
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, interfacefield),
        rbrace,
    ))(i2)?;

    pos.span_until_start(&i3);

    let st = VelosiParseTreeInterfaceDef::new(bases, fields, pos);
    Ok((
        i3,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::Memory(st)),
    ))
}

fn memory_interface_identity(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    // try parse the memory keyword, or return
    let (i1, _) = tuple((kw_memoryinterface, semicolon))(input)?;

    pos.span_until_start(&i1);

    let st = VelosiParseTreeInterfaceDef::new(Vec::new(), Vec::new(), pos);
    Ok((
        i1,
        VelosiParseTreeUnitNode::Interface(VelosiParseTreeInterface::Memory(st)),
    ))
}

/// Parses and consumes a comma separated list of identifiers of the form "(ident, ..., ident)"
///
/// # GRAMMAR
///
/// `INTERFACEPARAM := LPAREN SEPLIST(COMMA, PARAMETER) RPAREN
pub fn interfaceparams(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    let (i, p) = opt(delimited(
        lparen,
        cut(separated_list0(comma, parameter)),
        cut(rparen),
    ))(input)?;
    Ok((i, p.unwrap_or_default()))
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
fn interfacefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeInterfaceField> {
    let mut pos = input.clone();

    // get the field name
    let (i1, name) = ident(input)?;

    // recognize the field params
    let (i2, (offset, size)) = cut(delimited(lbrack, interfacefieldinfo, rbrack))(i1)?;

    let (i3, nodes) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, interfacefieldbody), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);
    Ok((
        i3,
        VelosiParseTreeInterfaceField::new(name, offset, size, nodes.unwrap_or_default(), pos),
    ))
}

/// Parses the state field information
///
/// # Grammar
///
/// `INTERFACEFIELDINFO := LBRACK IDENT? NUM? NUM RBRACK`
pub fn interfacefieldinfo(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, (Option<(String, u64)>, u64)> {
    let off = tuple((terminated(ident, cut(comma)), cut(terminated(num, comma))));
    tuple((opt(off), cut(num)))(input)
}

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
        terminated(separated_list0(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    )(i1)?;

    Ok((i2, VelosiParseTreeInterfaceFieldNode::Layout(slices)))
}

/// Pares and consumes a state field slice definition
///
/// # Grammar
///
/// `STATEFIELDSLICE := NUM DOTDOT NUM IDENT`
pub fn statefieldslice(
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

    // try parsing the ReadAction keyword
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

    // try parsing the WriteAction keyword
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
