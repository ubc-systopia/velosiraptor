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
use crate::ast::Import;
use crate::error::IResult;
use crate::parser::terminals::{ident, kw_import, semicolon};
use crate::token::TokenStream;

// the used nom components
use crate::nom::error::ErrorKind;
use nom::sequence::terminated;
use nom::{error_position, Err, IResult, InputLength, Slice};
// the used nom componets
use nom::{combinator::cut, sequence::terminated};

/// parses and consumes an import statement (`import foo;`) and any following whitespaces
pub fn import(input: TokenStream) -> IResult<TokenStream, Import> {
    // try to match the input keyword, there is no match, return.
    let (i1, _) = kw_import(input.clone())?;

    // ok, so we've seen the `import` keyword, so the next must be an identifier.
    // there should be at least one whitespace before the identifier
    let (rem, name) = cut(terminated(ident, semicolon))(i1)?;

    // create the token stream covering the entire import
    let pos = input.from_self_until(&rem);

    Ok((
        rem,
        Import {
            name,
            ast: None,
            pos: pos,
        },
    ))
}

#[cfg(test)]
use crate::sourcepos::SourcePos;
#[cfg(test)]
use crate::token::{Keyword, Token, TokenContent};
#[cfg(test)]
use nom::{error::ErrorKind, error_position, Err, Slice};
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
        Token::new(TokenContent::Eof, sp.slice(14..14)),
    ];
    let ts = TokenStream::from_slice(&tokens);

    let pos = ts.slice(0..3);
    let ts2 = ts.slice(3..);

    assert_eq!(
        import(ts),
        Ok((
            ts2,
            Import {
                name: "foobar".to_string(),
                ast: None,
                pos
            }
        ))
    );
}

#[test]
fn test_errors() {
    // corresponds to: `import foobar;`
    let content = "import foobar import";
    let sp = SourcePos::new("stdio", content);

    let tokens = vec![
        Token::new(TokenContent::Keyword(Keyword::Import), sp.slice(0..6)),
        Token::new(
            TokenContent::Identifier("foobar".to_string()),
            sp.slice(7..12),
        ),
        Token::new(TokenContent::Keyword(Keyword::Import), sp.slice(13..20)),
    ];

    let ts = TokenStream::from_slice(&tokens);
    assert!(import(ts).is_err());
}
