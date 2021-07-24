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

//! Unit Parser
//!
//! Parses a Unit definition including its state, constants etc.

// the used nom functionality
use nom::{
    combinator::{cut, opt},
    sequence::{delimited, pair, preceded, terminated},
};

// the used library-internal functionaltity
use crate::ast::{Interface, Unit, State};
use crate::error::IResult;
use crate::parser::{
    state::state,
    terminals::{colon, ident, kw_unit, lbrace, rbrace, semicolon},
};
use crate::token::TokenStream;

/// parses and consumes an import statement (`unit foo {};`)
pub fn unit(input: TokenStream) -> IResult<TokenStream, Unit> {
    // try to match the input keyword, there is no match, return.
    let (i1, _) = kw_unit(input.clone())?;

    // we've seen the `unit` keyword, next there is an identifyer maybe followed
    // the drive clause (: identifier)
    let derive = preceded(colon, cut(ident));
    let (i2, (unitname, derived)) = cut(pair(ident, opt(derive)))(i1)?;

    // TODO: here we have ConstItem | InterfaceItem | StateItem | FunctionItem
    // TODO: either put that as
    let unit_body = opt(state);

    // then we have the unit block, wrapped in curly braces and a ;
    let (i3, body) = cut(terminated(delimited(lbrace, unit_body, rbrace), semicolon))(i2)?;

    let pos = input.from_self_until(&i3);
    Ok((
        i3,
        Unit {
            name: unitname,
            derived: derived,
            consts: Vec::new(),
            state: body.unwrap_or(State::None),
            interface: Interface::None,
            methods: Vec::new(),
            pos,
        },
    ))
}

#[cfg(test)]
use crate::lexer::Lexer;

#[test]
fn test_ok() {
    let tokens = Lexer::lex_string("stdio", "unit foo {};").unwrap();
    let ts = TokenStream::from_vec(tokens);
    assert!(unit(ts).is_ok());
}