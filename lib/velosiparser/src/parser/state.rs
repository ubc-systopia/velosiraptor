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
    multi::separated_list0,
    sequence::{delimited, preceded, terminated, tuple},
};

// lexer, parser terminals and ast
use crate::error::IResult;
use crate::parser::{
    param::parameter,
    terminals::{
        assign, comma, dotdot, ident, kw_memorystate, kw_none, kw_registerstate, kw_state, lbrace,
        lbrack, lparen, num, rbrace, rbrack, rparen, semicolon,
    },
};
use crate::parsetree::{
    VelosiParseTreeFieldSlice, VelosiParseTreeParam, VelosiParseTreeState, VelosiParseTreeStateDef,
    VelosiParseTreeStateField, VelosiParseTreeUnitNode,
};
use crate::VelosiTokenStream;

/// parses and consumes the [VelosiParseTreeState] of a unit
///
/// # Grammar
///
/// `STATE := KW_STATE ASSIGN (NONE | REGISTERSTATE | MEMORYSTATE) SEMICOLON?`
pub fn state(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    //    let mut pos = input.clone();

    // try to match the state keyword, if there is no match, return.
    let (i1, _) = kw_state(input)?;

    // We now parse the different state types.
    cut(delimited(
        assign,
        alt((register_state, memory_state, none_state)),
        opt(semicolon),
    ))(i1)
}

/// parses and consumes a register state definition of a unit
///
/// # Grammar
///
/// `REGISTERSTATE := KW_REGISTERSTATE STATEPARAMS LBRACE STATEFIELDS RBRACE`
fn register_state(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_registerstate(input)?;
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
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Register(st)),
    ))
}

/// parses and consumes a memory state definition of a unit
///
/// # Grammar
///
/// `MEMORYSTATE := KW_REGISTERSTATE STATEPARAMS LBRACE STATEFIELDS RBRACE`
fn memory_state(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeUnitNode> {
    let mut pos = input.clone();

    let (i1, _) = kw_memorystate(input)?;
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
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(st)),
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
/// `STATEFIELD := IDENT STATEFIELDINFO (LBRACE SEPLIST(COMMA, STATEFIELDSLICE) RBRACE)?`
pub fn statefield(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, VelosiParseTreeStateField> {
    let mut pos = input.clone();

    // get the field name
    let (i1, name) = ident(input)?;

    // LBRACK IDENT? NUM? NUM RBRACK
    let (i2, (offset, size)) = cut(delimited(lbrack, statefieldinfo, rbrack))(i1)?;

    let (i3, slices) = opt(delimited(
        lbrace,
        terminated(separated_list0(comma, statefieldslice), opt(comma)),
        cut(rbrace),
    ))(i2)?;

    pos.span_until_start(&i3);

    let slices = if let Some(slices) = slices {
        slices
    } else {
        Vec::new()
    };

    Ok((
        i3,
        VelosiParseTreeStateField::new(name, offset, size, slices, pos),
    ))
}

/// Parses the state field information
///
/// # Grammar
///
/// `STATEFIELDINFO := LBRACK IDENT? NUM? NUM RBRACK`
pub fn statefieldinfo(
    input: VelosiTokenStream,
) -> IResult<VelosiTokenStream, (Option<(String, u64)>, u64)> {
    let off = tuple((terminated(ident, cut(comma)), cut(terminated(num, comma))));
    tuple((opt(off), cut(num)))(input)
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
    let state_string = "state = MemoryState (base : addr) {\
    pte [base, 0, 4] {\
        0 .. 1   present,\
        12.. 32  base\
        }\
    }";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(_))
    ));

    let state_string = "state = MemoryState (base : addr) {\
        pte [base, 0, 4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        }";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(_))
    ));

    let state_string = "state = MemoryState (base : addr) {\
        pte [base, 0, 4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        };";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(_))
    ));

    let state_string = "state = MemoryState (base : addr) {\
        pte [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            },\
        }";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(_))
    ));

    let state_string = "state = MemoryState (base : addr) {\
        pte [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            },\
        pte2 [4] {\
            0 .. 1   present,\
            12.. 32  base,\
            }\
        }";

    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Memory(_))
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
    let state_string = "state = RegisterState {\
        base [1] {\
            0 .. 0 enabled,\
            1 .. 1 read,\
            2 .. 2 write,\
        }
    };";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    let (_, parsed_state) = state(ts).unwrap();

    assert!(matches!(
        parsed_state,
        VelosiParseTreeUnitNode::State(VelosiParseTreeState::Register(_))
    ));
}

#[test]
fn fake_field_type_test() {
    let state_string = "state = BadType;";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();
    assert!(state(ts).is_err());
}

#[test]
fn missing_semicolon_test() {
    let state_string = "state = RegisterVelosiParseTreeState {\
        base [_, 0, 1] {\
            0  0 enabled;\
            1  1 read;\
            2  2 write;\
        };
    }";
    let state_string = "state = BadType;";
    let ts = VelosiLexer::lex_string(state_string.to_string()).unwrap();

    assert!(state(ts).is_err());
}
