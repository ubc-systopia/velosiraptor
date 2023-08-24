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

//! # VelosiParser: Import Clause

// external dependencies
use nom::{combinator::cut, sequence::terminated};

// used crate functionality
use crate::error::IResult;
use crate::parser::terminals::{ident, kw_import, semicolon};
use crate::parsetree::{VelosiParseTreeContextNode, VelosiParseTreeImport};
use crate::VelosiTokenStream;

/// parses and consumes an import directive
///
/// The import directive tells the compiler to include the contents of the imported file
///
/// # Arguments
///
/// * `input` - input token stream to be parsed
///
/// # Results
///
/// * Ok:  The parser succeeded. The return value is a tuple of the remaining input and the
///        recognized import directive as a parse tree node.
/// * Err: The parser did not succed. The return value indicates whether this is:
///
///    * Error: a recoverable error indicating that the parser did not recognize the input but
///             another parser might, or
///    * Failure: a fatal failure indicating the parser recognized the input but failed to parse it
///               and that another parser would fail.
///
/// # Grammar
///
/// `IMPORT := KW_IMPORT IDENT SEMICOLON`
///
/// # Examples
///
///  * `import foo;`
///
pub fn import(input: VelosiTokenStream) -> IResult<VelosiTokenStream, VelosiParseTreeContextNode> {
    // record the start
    let mut loc = input.clone();

    // try to match the input keyword, there is no match, return.
    let (i1, _) = kw_import(input)?;

    // We've seen the `import` keyword, so the next must be an identifier followed by a semicolon
    let (rem, name) = cut(terminated(ident, semicolon))(i1)?;

    // adjust the location information to include the entire source span
    loc.span_until_start(&rem);

    let import = VelosiParseTreeImport(name);
    Ok((rem, VelosiParseTreeContextNode::Import(import)))
}

#[cfg(test)]
use velosilexer::VelosiLexer;

#[test]
fn test_ok() {
    let content = "import foobar;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();

    let (rem, res) = import(ts).unwrap();
    assert_eq!(rem.len(), 0);
    if let VelosiParseTreeContextNode::Import(import) = res {
        assert_eq!(import.name(), "foobar");
    } else {
        panic!("Expected an import node, got {:?}", res);
    }
}

#[test]
fn test_errors() {
    let content = "import foobar hick;";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = import(ts);
    assert!(res.is_err());

    let content = "import foobar";
    let ts = VelosiLexer::lex_string(content.to_string()).unwrap();
    let res = import(ts);
    assert!(res.is_err());
}
