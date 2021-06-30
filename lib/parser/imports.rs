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
use nom::sequence::terminated;

// the result type
use nom::IResult;

// get the tokens
use crate::parser::terminals::{identifier, import, semicolon};

use crate::lexer::token::TokenStream;

use nom::error::ErrorKind;
use nom::{error_position, Err};

use crate::parser::ast::Import;

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn parse_import(input: TokenStream) -> IResult<TokenStream, Import> {
    // try to parse the

    // try to match the input keyword, there is no match, return.
    let i1 = match import(input) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // ok, so we've seen the `import` keyword, so the next must be an identifier.
    // there should be at least one whitespace before the identifier
    match terminated(identifier, semicolon)(i1) {
        Ok((r, ident)) => Ok((r, Import::new(ident, input.get_pos()))),
        Err(_) => Err(Err::Failure(error_position!(
            input,
            ErrorKind::AlphaNumeric
        ))),
    }
}

#[cfg(test)]
use crate::lexer::sourcepos::SourcePos;
#[cfg(test)]
use crate::lexer::token::{Token, TokenContent};
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    // corresponds to: `import foobar;`
    let tokens = vec![
        Token::new(TokenContent::Import, SourcePos::new("stdio", "import")),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            SourcePos::new_at("stdio", "foobar", 7, 8, 1),
        ),
        Token::new(
            TokenContent::SemiColon,
            SourcePos::new_at("stdio", ";", 13, 14, 1),
        ),
    ];
    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        parse_import(ts),
        Ok((
            ts.slice(3..),
            Import {
                name: "foobar".to_string(),
                pos: ts.get_pos()
            }
        ))
    );
}

#[test]
fn test_errors() {
    // corresponds to: `import foobar;`
    let tokens = vec![
        Token::new(TokenContent::Import, SourcePos::new("stdio", "import")),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            SourcePos::new_at("stdio", "foobar", 7, 8, 1),
        ),
    ];
    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        parse_import(ts),
        Err(Err::Failure(error_position!(ts, ErrorKind::AlphaNumeric)))
    );
}

// #[test]
// fn parse_import_newlines() {
//     assert_eq!(
//         parse_import(SourcePos::new("stdin", "import\nfoo\n;")),
//         Ok((
//             SourcePos::new_at("stdin", "", 12, 3, 2),
//             Import {
//                 filename: "foo".to_string(),
//                 pos: (1, 1)
//             }
//         ))
//     );
// }

// #[test]
// fn parse_import_syntax_error_eos() {
//     assert!(parse_import(SourcePos::new("stdin", "import foo bar")).is_err());
// }

// #[test]
// fn parse_import_syntax_error_ident() {
//     assert!(parse_import(SourcePos::new("stdin", "import ;")).is_err());
// }
