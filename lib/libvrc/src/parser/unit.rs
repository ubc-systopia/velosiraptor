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


// get the tokens
use crate::parser::terminals::{colon, ident, kw_unit, lbrace, rbrace};
use crate::parser::state::state;
use crate::token::TokenStream;
use crate::error::IResult;

use nom::combinator::opt;
use nom::sequence::{delimited, preceded};

use crate::ast::{Interface, State, Unit};

/// parses and consumes an import statement (`unit foo {};`) and any following whitespaces
pub fn unit(input: TokenStream) -> IResult<TokenStream, Unit> {
    // get the current position
    let pos = input.input_sourcepos();

    // try to match the input keyword, there is no match, return.
    let i1 = match kw_unit(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // ok, so we've seen the `unit` keyword, so the next must be an identifier.
    let (i1, unitname) = match ident(i1) {
        Ok((i, u)) => (i, u),
        Err(e) => return Err(e),
            // if we have parser failure, indicate this!
            //let (i, k) = match e {
            //    Err::Error(e) => (e.input, e.code),
            //    x => panic!("unknown condition: {:?}", x),
            //};
            //return Err(Err::Failure(error_position!(i, k)))
    };

    // is it a derived type, then we may see a ` : type` clause
    let (i2, supertype) = match opt(preceded(colon, ident))(i1) {
        Ok((i, s)) => (i, s),
        // possibly check here for an error!
        Err(e) => return Err(e)
            // if we have parser failure, indicate this!
            //let (i, k) = match e {
            //    Err::Error(e) => (e.input, e.code),
            //    x => panic!("unkown condition: {:?}", x),
            //};
            //return Err(Err::Failure(error_position!(i, k)));
        //}
    };

    // TODO: here we have ConstItem | InterfaceItem | StateItem | FunctionItem
    let unit_body = state;

    // then we have the unit block, wrapped in curly braces
    let (i3, _) = match delimited(lbrace, unit_body, rbrace)(i2) {
        Ok((i, b)) => (i, b),
        Err(e) => return Err(e),
        //     // if we have parser failure, indicate this!
        //     let (i, k) = match e {
        //         Err::Error(e) => (e.input, e.code),
        //         x => panic!("unkown condition: {:?}", x),
        //     };
        //     return Err(Err::Failure(error_position!(i, k)));
        // }
    };

    Ok((
        i3,
        Unit {
            name: unitname,
            derived: None,
            consts: Vec::new(),
            state: State::None,
            interface: Interface::None,
            methods: Vec::new(),
            pos,
        },
    ))
}
