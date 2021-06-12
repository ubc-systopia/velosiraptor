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

// the used nom componets
use nom::{
    bytes::complete::tag,
    character::complete::{multispace0, multispace1},
    sequence::{preceded, tuple},
    IResult,
};

// get the tokens
use super::identifier::parse_identifier;
use super::tokens;
use super::SourcePos;

use super::ast::Import;

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn parse_import(input: SourcePos) -> IResult<SourcePos, Import> {
    // record the current position
    let pos = input.get_pos();

    // try to match the input keyword, there is no match, return.
    let input = match tag(tokens::IMPORT)(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // ok, so we've seen the `import` keyword, so the next must be an identifier.
    // there should be at least one whitespace before the identifier
    let (input, ident) = match preceded(multispace1, parse_identifier)(input) {
        Ok((remainder, ident)) => (remainder, ident),
        Err(x) => {
            println!("parsing error: identifier expected.");
            println!("{}", input);
            return Err(x);
        }
    };

    // the end of statement is whitespace, the EOS token, followed by more whitespace
    match tuple((multispace0, tag(tokens::EOS), multispace0))(input) {
        Ok((remainder, _)) => Ok((remainder, Import::new(ident, pos))),
        Err(x) => {
            println!("parsing error: '{}' expected.", tokens::EOS);
            println!("{}", input);
            Err(x)
        }
    }
}

#[test]
fn parse_import_formatted() {
    assert_eq!(
        parse_import(SourcePos::new("stdin", "import foo;")),
        Ok((
            SourcePos::new_at("stdin", "", 11, 1, 12),
            Import {
                filename: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
}

#[test]
fn parse_import_newlines() {
    assert_eq!(
        parse_import(SourcePos::new("stdin", "import\nfoo\n;")),
        Ok((
            SourcePos::new_at("stdin", "", 12, 3, 2),
            Import {
                filename: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
}

#[test]
fn parse_import_syntax_error_eos() {
    assert!(parse_import(SourcePos::new("stdin", "import foo bar")).is_err());
}

#[test]
fn parse_import_syntax_error_ident() {
    assert!(parse_import(SourcePos::new("stdin", "import ;")).is_err());
}
