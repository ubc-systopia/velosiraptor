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

//! # Parser Errors for the VelosiParser

//
use std::fmt::{Display, Formatter, Result};

// external dependencies
use colored::*;
use nom::{
    error::{ErrorKind, ParseError},
    Err,
};

use crate::{VelosiTokenKind, VelosiTokenStream};
use velosilexer::VelosiLexerErr;

/// define the type of IResult
pub type IResult<I, O> = std::result::Result<(I, O), Err<VelosiParserErr>>;

pub(crate) struct VelosiParserErrBuilder {
    message: String,
    hint: Option<String>,
    tokstream: Option<VelosiTokenStream>,
}

impl VelosiParserErrBuilder {
    pub fn new(message: String) -> Self {
        Self {
            message,
            hint: None,
            tokstream: None,
        }
    }

    pub fn add_hint(&mut self, hint: String) -> &mut Self {
        self.hint = Some(hint);
        self
    }

    pub fn add_tokstream(&mut self, tokstream: VelosiTokenStream) -> &mut Self {
        self.tokstream = Some(tokstream);
        self
    }

    pub fn build(&mut self) -> VelosiParserErr {
        VelosiParserErr::Custom(VelosiParserErrCustom {
            message: self.message.clone(),
            kinds: Vec::new(),
            hint: self.hint.take(),
            tokstream: self.tokstream.take().unwrap_or_default(),
        })
    }
}

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub struct VelosiParserErrCustom {
    /// error message
    message: String,
    /// error kinds fron Nom
    kinds: Vec<ErrorKind>,
    /// Hint
    hint: Option<String>,
    /// the location where the error happened
    tokstream: VelosiTokenStream,
}

/// Implementation of [Display] for [VelosiParserErrCustom]
impl Display for VelosiParserErrCustom {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();
        let blue = |s: &str| s.bold().blue();

        // the error message
        writeln!(f, "{}{} {}", red("error"), ":".bold(), self.message.bold())?;

        let location = self.tokstream.span();

        // the location, if it is set
        if !location.is_default() {
            let pipe = blue("|");

            // location information
            writeln!(f, "     {} {}", blue("-->"), location.loc())?;
            writeln!(f, "      {pipe}")?;

            let linenum = location.line().to_string();

            let linectxt = location.srcline();
            if linectxt.len() <= 100 {
                // calculate the indentation
                let col = location.column();
                let indent = (0..col - 1).map(|_| " ").collect::<String>();

                // get the underline
                let ulen = std::cmp::min(location.len(), linectxt.len());
                let underline = (0..ulen).map(|_| "^").collect::<String>();

                // the line context with highligted part that is wrong
                writeln!(f, " {:>4} {}  {}", blue(&linenum), pipe, linectxt)?;
                write!(f, "      {}  {}{}", pipe, indent, red(&underline))?;
            } else {
                // we're longer than 100 characters, so truncate the output
                let col = location.column() as usize;

                let printrange = if col > 50 {
                    let end = std::cmp::min(col + 50, linectxt.len());
                    // just print stuff around colum +/- 50
                    col - 50..end
                } else {
                    // take verything from the beginning
                    0..100
                };

                let indent = (printrange.start..col - 1).map(|_| " ").collect::<String>();

                let ulen = std::cmp::min(location.len(), printrange.end - printrange.start);
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
                    red(&underline),
                )?;
            }
        }

        // apply the hint if needed
        match &self.hint {
            Some(h) => writeln!(f, " {}", red(h.as_str())),
            None => writeln!(f),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiParserErrExpected {
    kind: Vec<VelosiTokenKind>,
    tokstream: VelosiTokenStream,
}

impl VelosiParserErrExpected {
    pub fn new(tokstream: VelosiTokenStream, kind: VelosiTokenKind) -> Self {
        Self {
            kind: vec![kind],
            tokstream,
        }
    }

    pub fn merge(&mut self, other: Self) {
        self.kind.extend(other.kind);
    }
}

/// Implementation of [Display] for [VelosiParserErrExpected]
impl Display for VelosiParserErrExpected {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();
        let blue = |s: &str| s.bold().blue();

        write!(f, "{}{} ", red("error"), ": expected".bold())?;
        if self.kind.len() == 1 {
            write!(f, "`{}`", self.kind[0].as_hint_str().bold())?;
        } else {
            write!(f, "{}", "one of ".bold())?;
            for (i, t) in self.kind.iter().enumerate() {
                if i == 0 {
                    write!(f, "`{}`", t.as_hint_str().bold())?;
                } else if i == self.kind.len() - 1 {
                    write!(f, ", or `{}`", t.as_hint_str().bold())?;
                } else {
                    write!(f, ", `{}`", t.as_hint_str().bold())?;
                }
            }
        }

        write!(f, "{}", ", found ".bold())?;
        let ulen = if let Some(t) = self.tokstream.peek() {
            writeln!(f, "`{}`", t.span().as_str().bold())?;
            t.span().as_str().len()
        } else {
            writeln!(f, "`Eof`")?;
            3
        };

        let location = self.tokstream.span();
        if !location.is_default() {
            let pipe = blue("|");

            // location information
            writeln!(f, "     {} {}", blue("-->"), location.loc())?;
            writeln!(f, "      {pipe}")?;

            let linenum = location.line().to_string();

            let linectxt = location.srcline();
            if linectxt.len() <= 100 {
                // calculate the indentation
                let col = location.column();
                let indent = (0..col - 1).map(|_| " ").collect::<String>();

                // get the underline
                let ulen = std::cmp::min(ulen, linectxt.len());
                let underline = (0..ulen).map(|_| "^").collect::<String>();

                // the line context with highligted part that is wrong
                writeln!(f, " {:>4} {}  {}", blue(&linenum), pipe, linectxt)?;
                write!(f, "      {}  {}{}", pipe, indent, red(&underline))?;
            } else {
                // we're longer than 100 characters, so truncate the output
                let col = location.column() as usize;

                let printrange = if col > 50 {
                    let end = std::cmp::min(col + 50, linectxt.len());
                    // just print stuff around colum +/- 50
                    col - 50..end
                } else {
                    // take verything from the beginning
                    0..100
                };

                let indent = (printrange.start..col - 1).map(|_| " ").collect::<String>();

                let ulen = std::cmp::min(ulen, printrange.end - printrange.start);
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
                    red(&underline),
                )?;
            }
        }

        let h = if self.kind.len() == 1 {
            format!("help: add `{}` here.", self.kind[0].as_hint_str())
        } else {
            format!("expected one of {} possible tokens", self.kind.len())
        };
        writeln!(f, " {}", red(h.as_str()))
    }
}

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub enum VelosiParserErr {
    Expected(VelosiParserErrExpected),
    Kind(ErrorKind),
    Custom(VelosiParserErrCustom),
    Lexer(VelosiLexerErr),
    Stack(Vec<VelosiParserErr>),
}

impl VelosiParserErr {
    pub fn from_expected(position: VelosiTokenStream, kind: VelosiTokenKind) -> Self {
        VelosiParserErr::Expected(VelosiParserErrExpected::new(position, kind))
    }
}

impl From<VelosiLexerErr> for VelosiParserErr {
    fn from(err: VelosiLexerErr) -> Self {
        VelosiParserErr::Lexer(err)
    }
}

/// Implementation of [Display] for [VelosiParserErr]
impl Display for VelosiParserErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            VelosiParserErr::Expected(e) => e.fmt(f),
            VelosiParserErr::Custom(e) => e.fmt(f),
            VelosiParserErr::Lexer(e) => e.fmt(f),
            VelosiParserErr::Kind(k) => writeln!(f, "Nom kind: {k:?}"),
            VelosiParserErr::Stack(s) => {
                for e in s {
                    e.fmt(f)?;
                }
                Ok(())
            }
        }
    }
}

/// Implementation of [ParseError] for [VelosiParserErr]
impl ParseError<VelosiTokenStream> for VelosiParserErr {
    /// Creates an error from the input position and an ErrorKind
    fn from_error_kind(_input: VelosiTokenStream, kind: ErrorKind) -> Self {
        VelosiParserErr::Kind(kind)
    }

    /// Combines the existing error with a new one created at position
    fn append(_input: VelosiTokenStream, _kind: ErrorKind, other: Self) -> Self {
        other
    }

    fn or(mut self, other: Self) -> Self {
        use VelosiParserErr::*;
        let mut other = other;
        match (&mut self, &mut other) {
            (Expected(s), Expected(o)) => {
                for k in o.kind.drain(..) {
                    if !s.kind.contains(&k) {
                        s.kind.push(k);
                    }
                }
                self
            }
            (Expected(_), Kind(ErrorKind::Eof)) => self,
            (Kind(ErrorKind::Eof), Expected(_)) => other,
            (Kind(_), Kind(_)) => self,
            _ => panic!("not yet implemented: {:?} {:?}", self, other),
        }
    }
}
