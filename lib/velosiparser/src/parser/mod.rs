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

//! Parser Module of the Velosiraptor Compiler

// used exernal dependencies
use nom::{branch::alt, combinator::map, multi::many0, Err};

// the used library-internal functionality
use crate::error::{IResult, VelosiParserErrBuilder};
use crate::parsetree::{
    VelosiParseTree, VelosiParseTreeConstDef, VelosiParseTreeContextNode, VelosiParseTreeUnit,
};
use crate::VelosiTokenStream;

// the parser modules
// mod bitslice;
mod constdef;
mod expr;
// mod field;
// mod flags;
mod import;
mod interface;
mod map;
mod method;
mod param;
mod state;
mod terminals;
mod unit;

/// Parses a VelosiTokenStream into a VelosiParseTree
///
/// The function takes the parse context as a explicit argument
///
/// # Arguments
///  * `input`   - The input token stream to be parsed
///  * `context` - String identifying the parse context
///
/// # Grammar
///
/// CONTEXT := [ IMPORT | CONSTDEF | UNIT ]*
///
pub fn parse_with_context(
    input: VelosiTokenStream,
    context: String,
) -> IResult<VelosiTokenStream, VelosiParseTree> {
    match parse(input) {
        Ok((ts, mut pt)) => {
            pt.set_context(context);
            Ok((ts, pt))
        }
        e => e,
    }
}

/// Parses a VelosiTokenStream into a VelosiParseTree
///
/// The function tries to extract the parsing context from the supplied token stream.
///
/// # Arguments
///  * `input`   - The input token stream to be parsed
///
/// # Grammar
///
/// CONTEXT := [ IMPORT | CONSTDEF | UNIT ]*
///
pub fn parse(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTree> {
    // parse as many tree nodes as possible, that are either imports, constants or units
    // let (rem, nodes) = many0(alt((import, constdef, unit)))(input)?;
    let (rem, nodes) = many0(alt((
        import::import,
        map(constdef::constdef, |s: VelosiParseTreeConstDef| {
            VelosiParseTreeContextNode::Const(s)
        }),
        map(unit::unit, |s: VelosiParseTreeUnit| {
            VelosiParseTreeContextNode::Unit(s)
        }),
    )))(input)?;

    // we expect everything to be parsed, of not this will trigger an error
    if !rem.is_empty() {
        let errmsg = "Unexpected tokens at the end of the file. Expected one of `import`, `const`, or `unit` definitions.".to_string();
        let err = VelosiParserErrBuilder::new(errmsg)
            .add_hint("Remove unexpected content.".to_string())
            .add_tokstream(rem)
            .build();
        return Err(Err::Failure(err));
    }

    Ok((rem, VelosiParseTree::new(nodes)))
}
