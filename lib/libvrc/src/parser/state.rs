// Velosiraptor Compiler
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

//! State definition parsing

// the used nom components
use nom::{
    branch::alt,
    combinator::cut,
    multi::separated_list0,
    sequence::{delimited, terminated},
};

// lexer, parser terminals and ast
use crate::ast::{Field, State};
use crate::error::IResult;
use crate::parser::field::field;
use crate::parser::terminals::{
    assign, comma, ident, kw_memory, kw_none, kw_register, kw_state, lbrace, lparen, rbrace,
    rparen, semicolon,
};
use crate::token::TokenStream;

/// parses and consumes the [State] of a unit
pub fn state(input: TokenStream) -> IResult<TokenStream, State> {
    // try to match the state keyword, if there is no match, return.
    let (i1, _) = kw_state(input)?;
    // We now parse the different state types.
    cut(delimited(
        assign,
        alt((register_state, memory_state, none_state)),
        semicolon,
    ))(i1)
}

/// parses and consumes [RegisterState] of a unit
fn register_state(input: TokenStream) -> IResult<TokenStream, State> {
    let (i1, _) = kw_register(input.clone())?;
    let (i2, fields) = fields_parser(i1)?;

    let pos = input.from_self_until(&i2);
    Ok((i2, State::RegisterState { fields, pos }))
}

/// parses and consumes [MemoryState] of a unit
fn memory_state(input: TokenStream) -> IResult<TokenStream, State> {
    let (i1, _) = kw_memory(input.clone())?;
    let (i2, bases) = argument_parser(i1)?;
    let (i3, fields) = fields_parser(i2)?;

    let pos = input.from_self_until(&i3);
    Ok((i3, State::MemoryState { bases, fields, pos }))
}

/// parses and consumes [None] state of a unit
fn none_state(input: TokenStream) -> IResult<TokenStream, State> {
    let (i1, s) = kw_none(input)?;

    Ok((i1, State::None { pos: s }))
}

/// Parses and consumes a comma separated list of identifiers of the form "(ident, ..., ident)"
pub fn argument_parser(input: TokenStream) -> IResult<TokenStream, Vec<String>> {
    cut(delimited(lparen, separated_list0(comma, ident), rparen))(input)
}

/// Parses and consumes a semicolon separated list of fields of the form "{ FIELD; ...; FIELD; }"
pub fn fields_parser(input: TokenStream) -> IResult<TokenStream, Vec<Field>> {
    cut(delimited(
        lbrace,
        terminated(separated_list0(semicolon, field), semicolon),
        rbrace,
    ))(input)
}

#[cfg(test)]
use crate::lexer::Lexer;
#[cfg(test)]
use nom::Slice;

// TODO ask Reto about current source pos assignment.
#[test]
fn memory_state_parser_test() {
    let state_string = "state = Memory(base) {\
    pte [base, 0, 4] {\
        0   0   present,\
        1   1   writable,\
        3   3   writethrough,\
        4   4   nocache,\
        5   5   accessed,\
        6   6   dirty,\
        7   7   pat,\
        8   8   global,\
        9  11   ignored,\
        12  31  base\
        };\
    };";
    let tok_vec = match Lexer::lex_string("stdin", state_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    let parsed_state = match state(tok_stream.clone()) {
        Ok((_, parsed_state)) => parsed_state,
        Err(_) => panic!("Parsing failed"),
    };

    let (bases, fields, pos) = match parsed_state {
        State::MemoryState { bases, fields, pos } => (bases, fields, pos),
        _ => panic!("Wrong type of State parsed"),
    };

    // todo Do I need to test this when it's already being done in fields.rs
    /*assert_eq!(fields,
    vec![Field { name: String::from("pte"),
        stateref: Some((String::from("base"), 0)),
        length: 4,
        layout: vec![],
        pos: tok_stream.slice(17..).input_sourcepos()
    }]);*/
    assert_eq!(bases, vec!["base"])
    //assert_eq!(parsed_state , vec!["base"]);
}

#[test]
fn none_state_parser_test() {
    let state_string = "state = None;";
    let tok_vec = match Lexer::lex_string("stdin", state_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    let parsed_state = match state(tok_stream) {
        Ok((_, parsed_state)) => parsed_state,
        Err(_) => panic!("Parsing failed"),
    };

    match parsed_state {
        State::None { pos: _ } => (),
        _ => panic!("Wrong type of State parsed"),
    };
}

#[test]
fn register_state_parser_test() {
    let state_string = "state = Register {\
        base [_, 0, 1] {\
            0  0 enabled,\
            1  1 read,\
            2  2 write\
        };
    };";
    let tok_vec = match Lexer::lex_string("stdin", state_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    let parsed_state = match state(tok_stream.clone()) {
        Ok((_, parsed_state)) => parsed_state,
        Err(_) => panic!("Parsing failed"),
    };

    let (fields, pos) = match parsed_state {
        State::RegisterState { fields, pos } => (fields, pos),
        _ => panic!("Wrong type of State parsed"),
    };

    // todo Should we be testing fields???
    assert_eq!(pos, tok_stream.slice(2..4));
}

#[test]
fn fake_field_type_test() {
    let state_string = "state = BadType;";
    let tok_vec = match Lexer::lex_string("stdin", state_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    assert!(state(tok_stream).is_err());
}

#[test]
fn missing_semicolon_test() {
    let state_string = "state = Register {\
        base [_, 0, 1] {\
            0  0 enabled,\
            1  1 read,\
            2  2 write\
        };
    }";
    let tok_vec = match Lexer::lex_string("stdin", state_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    assert!(state(tok_stream).is_err());
}

#[test]
fn fields_parser_err_test() {
    let fields_string = "\
            0  0 enabled,\
            1  1 read\
            2  2 write,\
            3  64 address\
    ";
    let tok_vec = match Lexer::lex_string("stdin", fields_string) {
        Ok(tok_vec) => tok_vec,
        Err(_) => panic!("Lexing failed"),
    };
    let tok_stream = TokenStream::from_vec_filtered(tok_vec);
    assert!(fields_parser(tok_stream).is_err());
}
