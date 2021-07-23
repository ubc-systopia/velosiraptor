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

// lexer, parser terminals and ast
use crate::ast::ast::{Field, State, BitSlice};
use crate::lexer::token::{Token, TokenStream, TokenContent, Keyword};
use crate::parser::field::field;
use crate::parser::terminals::{ident, kw_state, kw_register, kw_memory, assign, comma, lparen, rparen, lbrace, rbrace, semicolon, kw_none};
//use crate::parser::field::field;


use nom::multi::separated_list0;
// the used nom components
use nom::{error::ErrorKind, error_position, Err, IResult, Slice};
use nom::sequence::{delimited, terminated};
use nom::branch::alt;
use crate::lexer::Lexer;
use crate::ast::ast::State::MemoryState;

/// parses and consumes the [State] of a unit
pub fn state(input: TokenStream) -> IResult<TokenStream, State> {
    // try to match the state keyword, if there is no match, return.
    let (i1, _)= kw_state(input)?;
    // We now parse the different state types.
    delimited(assign, alt((register_state, memory_state, none_state)), semicolon)(i1)
}

/// parses and consumes [RegisterState] of a unit
fn register_state(input: TokenStream) -> IResult<TokenStream, State> {

    let pos = input.input_sourcepos();

    let (i1, _) = kw_register(input)?;
    let (i2, fields) = fields_parser(i1)?;

    Ok((i2, State::RegisterState{ fields, pos }))
    //Ok((i1, State::RegisterState{ fields, pos }))
}

/// parses and consumes [MemoryState] of a unit
fn memory_state(input: TokenStream) -> IResult<TokenStream, State> {

    let pos = input.input_sourcepos();

    let (i1, _) = kw_memory(input)?;
    let (i2, bases) = argument_parser(i1)?;
    let (i3, fields) = fields_parser(i2)?;

    Ok((i3, State::MemoryState{ bases, fields, pos }))
}

/// parses and consumes [None] state of a unit
fn none_state(input: TokenStream) -> IResult<TokenStream, State> {

    let pos = input.input_sourcepos();

    let (i1, _) = kw_none(input)?;
    //println!("parsed None keyword");

    Ok((i1, State::None))
}

/// Parses and consumes a comma separated list of identifiers of the form "(ident, ..., ident)"
pub fn argument_parser(input: TokenStream) -> IResult<TokenStream, Vec<String>> {
    match delimited(lparen, separated_list0(comma, ident), rparen)(input.clone()) {
        Ok((i1, arguments)) => Ok((i1, arguments)),
        Err(e) => {
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            return Err(Err::Failure(error_position!(i, k)));
        }
    }
}

/// Parses and consumes a semicolon separated list of fields of the form "{ FIELD; ...; FIELD; }"
pub fn fields_parser(input: TokenStream) -> IResult<TokenStream, Vec<Field>> {
    match delimited(lbrace, terminated(separated_list0(semicolon, field), semicolon), rbrace)(input.clone()) {
        Ok((i1, fields)) => Ok((i1, fields)),
        Err(e) => {
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            Err(Err::Failure(error_position!(i, k)))
        }
    }
}

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
        State::MemoryState {bases, fields, pos} => (bases, fields, pos),
        _ => panic!("Wrong type of State parsed"),
    };

    //println!("{:?}", fields);

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
        State::None => (),
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

    //println!{"{:?}", pos}
    // todo Should we be testing fields???
    assert_eq!(pos, tok_stream.slice(2..4).input_sourcepos());
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