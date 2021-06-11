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
    sequence::{preceded, terminated, tuple},
    IResult,
};

// get the tokens
use super::identifier::parse_identifier;
use super::tokens;
use super::SourcePos;

use super::ast::Ast;

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn import(input: SourcePos) -> IResult<SourcePos, Ast> {
    // record the current position
    let pos = input.get_pos();

    // the import block is an identifier, preceeded by the import keyword and whitespace
    // we do not allow comments between the import keyword and the identifier
    let import_block = preceded(tuple((tag(tokens::IMPORT), multispace1)), parse_identifier);

    // the end of statement is whitespace, the EOS token, followed by more whitespace
    let end_of_statement = tuple((multispace0, tag(tokens::EOS), multispace0));

    // now match the import statement that is an import block followed by an end of statement part
    match terminated(import_block, end_of_statement)(input) {
        Ok((input, ident)) => Ok((input, Ast::import_from_sourcepos(ident, pos))),
        Err(x) => Err(x),
    }
}

#[test]
fn parse_import_formatted() {
    assert_eq!(
        import(SourcePos::new("stdin", "import foo;")),
        Ok((
            SourcePos::new_at("stdin", "", 11, 1, 12),
            Ast::Import {
                filename: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
}

#[test]
fn parse_import_newlines() {
    assert_eq!(
        import(SourcePos::new("stdin", "import\nfoo\n;")),
        Ok((
            SourcePos::new_at("stdin", "", 12, 3, 2),
            Ast::Import {
                filename: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
}
