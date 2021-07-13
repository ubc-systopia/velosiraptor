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

//! Import statement parsing

// lexer, parser terminals and ast
use crate::ast::ast::Import;
use crate::lexer::token::TokenStream;
use crate::parser::terminals::{ident, kw_import, semicolon};

// the used nom componets
use crate::nom::error::ErrorKind;
use nom::sequence::terminated;
use nom::{error_position, Err, IResult, Slice};

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn import(input: TokenStream) -> IResult<TokenStream, Import> {
    // get the current position
    let pos = input.input_sourcepos();

    // try to match the input keyword, there is no match, return.
    let i1 = match kw_import(input.clone()) {
        Ok((input, _)) => input,
        Err(x) => return Err(x),
    };

    // ok, so we've seen the `import` keyword, so the next must be an identifier.
    // there should be at least one whitespace before the identifier
    match terminated(ident, semicolon)(i1) {
        Ok((r, name)) => Ok((
            r,
            Import {
                name,
                pos: pos.slice(0..4),
            },
        )),
        Err(e) => {
            // if we have parser failure, indicate this!
            let (i, k) = match e {
                Err::Error(e) => (e.input, e.code),
                Err::Failure(e) => (e.input, e.code),
                Err::Incomplete(_) => (input, ErrorKind::Eof),
            };
            Err(Err::Failure(error_position!(i, k)))
        }
    }
}

#[cfg(test)]
use crate::lexer::sourcepos::SourcePos;
#[cfg(test)]
use crate::lexer::token::{Keyword, Token, TokenContent};
#[cfg(test)]
#[cfg(test)]
use crate::nom::Slice;

#[test]
fn test_ok() {
    // corresponds to: `import foobar;`
    let content = "import foobar;";
    let sp = SourcePos::new("stdio", content);

    let tokens = vec![
        Token::new(TokenContent::Keyword(Keyword::Import), sp.slice(0..6)),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            sp.slice(7..12),
        ),
        Token::new(TokenContent::SemiColon, sp.slice(13..14)),
    ];
    let ts = TokenStream::from_slice(&tokens);
    let pos = ts.input_sourcepos();
    let ts2 = ts.slice(3..);
    assert_eq!(
        import(ts),
        Ok((
            ts2,
            Import {
                name: "foobar".to_string(),
                pos
            }
        ))
    );
}

#[test]
fn test_errors() {
    // corresponds to: `import foobar;`
    let content = "import foobar";
    let sp = SourcePos::new("stdio", content);

    let tokens = vec![
        Token::new(TokenContent::Keyword(Keyword::Import), sp.slice(0..6)),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            sp.slice(7..12),
        ),
    ];

    let ts = TokenStream::from_slice(&tokens);

    assert_eq!(
        import(ts.clone()),
        Err(Err::Failure(error_position!(ts, ErrorKind::Eof)))
    );
}
