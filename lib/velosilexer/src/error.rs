// Velosilexer Error
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Lexer Errors for the VelosiLexer

//
use std::fmt::{Display, Formatter, Result};

// external dependencies
use colored::*;
use nom::{
    error::{ContextError, Error, ErrorKind, FromExternalError, ParseError},
    Err,
};

use crate::SrcSpan;

/// define the type of IResult
pub type IResult<I, O> = std::result::Result<(I, O), Err<VelosiLexerError>>;

pub(crate) struct VelosiLexerErrorBuilder {
    message: String,
    hint: Option<String>,
    location: Option<SrcSpan>,
}

impl VelosiLexerErrorBuilder {
    pub fn new(message: String) -> Self {
        Self {
            message,
            hint: None,
            location: None,
        }
    }

    pub fn add_hint(&mut self, hint: String) -> &mut Self {
        self.hint = Some(hint);
        self
    }

    pub fn add_location(&mut self, location: SrcSpan) -> &mut Self {
        self.location = Some(location);
        self
    }

    pub fn build(&mut self) -> VelosiLexerError {
        VelosiLexerError {
            message: self.message.clone(),
            kinds: Vec::new(),
            hint: self.hint.take(),
            location: self.location.take().unwrap_or_default(),
        }
    }
}

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub struct VelosiLexerError {
    /// error message
    message: String,
    /// error kinds fron Nom
    kinds: Vec<ErrorKind>,
    /// Hint
    hint: Option<String>,
    /// the location where the error happened
    location: SrcSpan,
}

impl VelosiLexerError {}

/// Implementation of [Display] for [VelosiLexerError]
impl Display for VelosiLexerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();
        let blue = |s: &str| s.bold().blue();

        // the error message
        writeln!(f, "{}{} {}", red("error"), ":".bold(), self.message.bold())?;

        // the location, if it is set
        if !self.location.is_default() {
            let pipe = blue("|");

            // location information
            writeln!(f, "     {} {}", blue("-->"), self.location.loc())?;
            writeln!(f, "      {}", pipe)?;

            let linenum = self.location.line().to_string();

            let linectxt = self.location.srcline();
            if linectxt.len() <= 100 {
                // calculate the indentation
                let col = self.location.column();
                let indent = (0..col - 1).map(|_| " ").collect::<String>();

                // get the underline
                let ulen = std::cmp::min(self.location.len(), linectxt.len());
                let underline = (0..ulen).map(|_| "^").collect::<String>();

                // the line context with highligted part that is wrong
                writeln!(f, " {:>4} {}         {}", blue(&linenum), pipe, linectxt)?;
                write!(f, "      {}         {}{}", pipe, indent, blue(&underline))?;
            } else {
                // we're longer than 100 characters, so truncate the output
                let col = self.location.column() as usize;

                let printrange = if col > 50 {
                    let end = std::cmp::min(col + 50, linectxt.len());
                    // just print stuff around colum +/- 50
                    col - 50..end
                } else {
                    // take verything from the beginning
                    0..100
                };

                let indent = (printrange.start..col - 1).map(|_| " ").collect::<String>();

                let ulen = std::cmp::min(self.location.len(), printrange.end - printrange.start);
                let underline = (0..ulen).map(|_| "^").collect::<String>();

                // the line context with highligted part that is wrong
                writeln!(
                    f,
                    " {:>4} {}         ... {}... ",
                    blue(&linenum),
                    pipe,
                    &linectxt[printrange]
                )?;
                write!(
                    f,
                    "      {}             {}{}",
                    pipe,
                    indent,
                    blue(&underline),
                )?;
            };
        }

        // apply the hint if needed
        match &self.hint {
            Some(h) => writeln!(f, " {}", red(h.as_str())),
            None => writeln!(f),
        }
    }
}

/// Implementation of [nom::error::ContextError] for [VelosiLexerError]
impl ContextError<SrcSpan> for VelosiLexerError {
    /// Creates a new error from an input position, a static string and an existing error.
    ///
    /// This is used mainly in the context combinator, to add user friendly information
    /// to errors when backtracking through a parse tree
    fn add_context(_input: SrcSpan, _ctx: &'static str, _other: Self) -> Self {
        panic!("adding context");
    }
}

/// Implementation of [nom:error::ParseError] for [VelosiLexerError]
impl ParseError<SrcSpan> for VelosiLexerError {
    /// Creates an error from the input position and an ErrorKind
    fn from_error_kind(input: SrcSpan, kind: ErrorKind) -> Self {
        VelosiLexerError {
            message: String::new(),
            hint: None,
            kinds: vec![kind],
            location: input,
        }
    }

    /// Combines the existing error with a new one created at position
    fn append(input: SrcSpan, kind: ErrorKind, mut other: Self) -> Self {
        other.kinds.push(kind);
        // handle source location ?
        other
    }

    fn or(mut self, other: Self) -> Self {
        if self.message.is_empty() {
            self.message = other.message;
        }
        self.kinds.extend(other.kinds);
        self
    }
}

/// Implementation of [nom::FromExternalError] for [VrsError]
impl<E> FromExternalError<SrcSpan, E> for VelosiLexerError {
    fn from_external_error(input: SrcSpan, kind: ErrorKind, _e: E) -> Self {
        // VrsError::from_error_kind(input, kind)
        panic!("from_external_error!");
    }
}

/// Implementation of [std::convert::From] for [VrsError]
///
/// This converts from a nom error to a VrsError.
impl From<Err<Error<SrcSpan>>> for VelosiLexerError {
    fn from(e: nom::Err<Error<SrcSpan>>) -> Self {
        panic!("from source span!");

        // match e {
        //     Err::Failure(e) => VrsError::from_error_kind(e.input, e.code),
        //     Err::Error(e) => VrsError::from_error_kind(e.input, e.code),
        //     _ => panic!("shoudl nto happend..."),
        // }
    }
}
