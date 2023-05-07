// VelosiParser -- Parser for the VelosiRaptor specification language
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # State definition parsing

// the used nom components
use nom::{
    branch::alt,
    combinator::{cut, opt},
    multi::{separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
};

// lexer, parser terminals and ast
use crate::error::IResult;
use crate::parser::{
    param::parameter,
    terminals::{
        assign, comma, dotdot, ident, kw_mem, kw_none, kw_reg, kw_state, kw_statedef, lbrace,
        lbrack, lparen, num, rbrace, rbrack, rparen, semicolon,
    },
};
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeIdentifier, VelosiParseTreeParam,
    VelosiParseTreeState, VelosiParseTreeStateDef, VelosiParseTreeStateField,
    VelosiParseTreeStateFieldMemory, VelosiParseTreeStateFieldRegister, VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

/// parses and consumes the [VelosiParseTreeState] of a unit
///
/// # Grammar
///
/// `STATE := KW_STATE ASSIGN (NONE | STATEDEF) SEMICOLON`
pub fn state(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    //    let mut pos = input.clone();

    // try to match the state keyword, if there is no match, return.
    let (i1, _) = kw_state(input)?;

    // We now parse the different state types.
    cut(delimited(assign, alt((statedef, none_state)), semicolon))(i1)
}

/// parses and consumes a memory state definition of a unit
///
/// # Grammar
///
/// `STATEDEF := KW_STATEDEF STATEPARAMS LBRACE STATEFIELDS RBRACE`
fn statedef(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_statedef(input)?;
    let (i2, bases) = stateparams(i1)?;
    let (i3, fields) = cut(delimited(
        lbrace,
        separated_list0(comma, statefield),
        tuple((opt(comma), rbrace)),
    ))(i2)?;

    pos.span_until_start(&i3);

    let st = VelosiParseTreeStateDef::new(bases, fields, pos);
    Ok((
        i3,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(st)),
    ))
}

/// parses and consumes a none state definition of a unit
///
/// # Grammar
///
/// `NONE := KW_NONE`
fn none_state(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_none(input)?;

    pos.span_until_start(&i1);

    Ok((
        i1,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::None(pos)),
    ))
}

/// Parses and consumes a comma separated list of identifiers of the form "(ident, ..., ident)"
///
/// # GRAMMAR
///
/// `STATEPARAMS := LPAREN SEPLIST(COMMA, PARAMETER) RPAREN
pub fn stateparams(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, Vec<VelosiParseTreeParam>> {
    let (i, p) = opt(delimited(
        lparen,
        cut(separated_list0(comma, parameter)),
        cut(rparen),
    ))(input)?;
    Ok((i, p.unwrap_or_default()))
}

/// Parses and consumes a state field definition
///
/// # Grammar
///
/// `STATEFIELD := MEMORYFIELD | REGISTERFIELD`
pub fn statefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    alt((memoryfield, registerfield))(input)
}

/// Parses and consumes a state field definition
///
/// # Grammar
///
/// `MEMORYFIELD := KW_MEM IDENT STATEFIELDINFO (LBRACE SEPLIST(COMMA, STATEFIELDSLICE) RBRACE)?`
pub fn memoryfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    let mut pos = input.clone();

    // if we have the memory keyword
    let (i1, _) = kw_mem(input)?;

    let (i2, (name, fieldinfo)) = cut(tuple((ident, delimited(lbrack, memfieldinfo, rbrack))))(i1)?;

    let (i3, slices) = opt(delimited(
        lbrace,
        terminated(separated_list1(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let slices = if let Some(slices) = slices {
        slices
    } else {
        Vec::new()
    };

    let (base, offset, size) = fieldinfo;

    let res = VelosiParseTreeStateFieldMemory::new(name, base, offset, size, slices, pos);
    Ok((i3, VelosiParseTreeStateField::Memory(res)))
}

type MemFiledInfo = (VelosiParseTreeIdentifier, u64, u64);

/// Parses the state field information
///
/// # Grammar
///
/// `STATEFIELDINFO := LBRACK IDENT NUM NUM RBRACK`
pub fn memfieldinfo(input: VelosiTokenStream) -> IResult<VelosiTokenStream, MemFiledInfo> {
    tuple((terminated(ident, comma), terminated(num, comma), num))(input)
}

/// Parses and consumes a state field definition
///
/// # Grammar
///
/// `STATEFIELD := IDENT STATEFIELDINFO (LBRACE SEPLIST(COMMA, STATEFIELDSLICE) RBRACE)?`
pub fn registerfield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    let mut pos = input.clone();

    // if we have the memory keyword
    let (i1, _) = kw_reg(input)?;

    let (i2, (name, size)) = cut(tuple((ident, delimited(lbrack, num, rbrack))))(i1)?;

    let (i3, slices) = opt(delimited(
        lbrace,
        terminated(separated_list1(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let slices = if let Some(slices) = slices {
        slices
    } else {
        Vec::new()
    };

    let res = VelosiParseTreeStateFieldRegister::new(name, size, slices, pos);
    Ok((i3, VelosiParseTreeStateField::Register(res)))
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

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn memory_state_parser_test() {
    let state_string = "state = StateDef (base : addr) {\
    mem pte [base, 0, 4] {\
        0 .. 1   present,\
        12.. 32  base\
        }\
    };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));

    let state_string = "state = StateDef (base : addr) {\
        mem pte [base, 0, 4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));

    let state_string = "state = StateDef (base : addr) {\
        mem pte [base, 0, 4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));

    let state_string = "state = StateDef (base : addr) {\
        reg pte [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            },\
        };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));

    let state_string = "state = StateDef (base : addr) {\
        reg pte [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            },\
        reg pte2 [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));
}

#[test]
fn none_state_parser_test() {
    let state_string = "state = None;";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::None(_))
    ));
}

#[test]
fn register_state_parser_test() {
    let state_string = "state = StateDef {\
        reg base [1] {\
            0 .. 0 enabled,\
            1 .. 1 read,\
            2 .. 2 write,\
        }
    };";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::StateDef(_))
    ));
}

#[test]
fn fake_field_type_test() {
    let state_string = "state = BadType;";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    assert!(state(ts).is_err());
}
