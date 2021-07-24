// Velosiraptor Parser
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

use crate::token::TokenStream;
use crate::error::IResult;
use crate::ast::Interface;
use crate::parser::terminals::{kw_interface, assign, semicolon};
use nom::combinator::cut;
use nom::branch::alt;
use nom::sequence::delimited;

/// Parses and consumes the [Interface] of a Unit
pub fn interface(input: TokenStream) -> IResult<TokenStream, Interface> {
    // try to match the interface keyword
    let (i1,_) = kw_interface(input)?;
    // We can now parse the different interface types
    cut(delimited(
        assign,
        alt((memory, mmio_registers, cpu_registers, special_registers)),
        semicolon
    ))(i1)
}

fn memory(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn mmio_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn cpu_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}

fn special_registers(input: TokenStream) -> IResult<TokenStream, Interface> {
    todo!()
}
