// Velosiraptor Lexer
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

//! Lexer/Parser Error Implementation for Nom

use colored::*;
use std::fmt;

// get the NOM traits
use nom::error::{ContextError, Error, ErrorKind, FromExternalError, ParseError};

use nom::Err;

use crate::token::TokenContent;

/// define the type of IResult
pub type IResult<I, O> = std::result::Result<(I, O), Err<VrsError<I>>>;

/// Trait for the location data structures
///
/// This trait is to be implemented by the parsing streams
pub trait ErrorLocation {
    /// the line number in the source file
    fn line(&self) -> u32;

    /// the column number in the source file
    fn column(&self) -> u32;

    /// the length of the token
    fn length(&self) -> usize;

    /// the context (stdin or filename)
    fn context(&self) -> &str;

    /// the surrounding line context
    fn linecontext(&self) -> &str;
}

/// Error representation
///
/// This structure captuers the location of the error or warning occurred.
/// The the type of the location must implemenet the ErrorLocation trait to
/// support printing the location of the error.
#[derive(PartialEq)]
pub enum VrsError<I: ErrorLocation> {
    /// represents a wrapped NOM error
    Nom {
        /// the encapsulated nom error
        error: Error<I>,
    },
    ExpectedToken {
        location: I,
        tokens: Vec<TokenContent>,
    },
    /// represents a custom error
    Error {
        /// error message
        message: String,
        /// Hint
        hint: Option<String>,
        /// the location where the error happened
        location: I,
    },
    /// represents a custom error
    DoubleDef {
        /// error message
        ident: String,
        /// the location where the error happened
        current: I,
        /// site of the previous definition
        previous: I,
    },
    /// reprsents a custom warning
    Warning {
        /// error message
        message: String,
        /// Hint
        hint: Option<String>,
        /// the location where the error happened
        location: I,
    },
    /// represents a error stack
    Stack {
        /// error message
        message: String,
        /// the location where the error happened
        location: I,
        /// the next error in the chain
        next: Box<VrsError<I>>,
    },
}

/// Implementation of the VrsError
impl<I: ErrorLocation + fmt::Display> VrsError<I> {
    /// creates a new warning
    pub fn new_warn(location: I, message: String, hint: Option<String>) -> Self {
        VrsError::Warning {
            message,
            hint,
            location,
        }
    }
    /// creates a new warning
    pub fn new_err(location: I, message: String, hint: Option<String>) -> Self {
        VrsError::Error {
            message,
            hint,
            location,
        }
    }
    /// creates a new warning
    pub fn new_double(ident: String, current: I, previous: I) -> Self {
        VrsError::DoubleDef {
            ident,
            current,
            previous,
        }
    }

    pub fn stack(location: I, message: String, other: VrsError<I>) -> Self {
        VrsError::Stack {
            message,
            location,
            next: Box::new(other),
        }
    }

    pub fn from_token(input: I, c: TokenContent) -> Self {
        VrsError::ExpectedToken {
            location: input,
            tokens: vec![c],
        }
    }

    pub fn print(&self) {
        eprintln!("{}", self)
    }

    fn fmtloc(f: &mut fmt::Formatter<'_>, loc: &I) -> std::fmt::Result {
        let line = loc.line();
        let col = loc.column();
        let ctxt = loc.context();
        // --> src/error/mod.rs:112:62
        writeln!(f, "     {} {}:{}:{}", "-->".bold().blue(), ctxt, line, col)
    }

    fn fmthdr(
        f: &mut fmt::Formatter<'_>,
        typ: colored::ColoredString,
        loc: &I,
        msg: &str,
    ) -> std::fmt::Result {
        // error: <message>
        writeln!(f, "{}{} {}", typ, ":".bold(), msg.bold())?;
        Self::fmtloc(f, loc)
    }

    fn fmtctx(
        f: &mut fmt::Formatter<'_>,
        warn: bool,
        loc: &I,
        hint: Option<&String>,
    ) -> std::fmt::Result {
        let pipe = "|".bold().blue();

        let color = if warn {
            |s: &str| s.bright_yellow().bold()
        } else {
            |s: &str| s.bright_red().bold()
        };

        let line = loc.line();
        let lineblue = line.to_string().as_str().bold().blue();
        let col = loc.column();
        let linectxt = loc.linecontext();

        let indent = (0..col - 1).map(|_| " ").collect::<String>();

        let underline = color((0..loc.length()).map(|_| "^").collect::<String>().as_str());

        // error: <message>
        writeln!(f, "      {}", pipe)?;
        // // the line context
        writeln!(f, " {:>4} {}         {}", lineblue, pipe, linectxt)?;

        // // the error message
        write!(f, "      {}         {}{}", pipe, indent, underline)?;
        match hint {
            Some(h) => writeln!(f, " {}", color(h)),
            None => writeln!(f, ""),
        }
    }
}

/// Implementation of [std::fmt::Display] for [VrsError]
impl<I: ErrorLocation + fmt::Display> fmt::Display for VrsError<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        let pipe = "|".bold().blue();

        // ok that's gotta be done simpler...
        let applycolor = |y| {
            if y {
                |s: &str| s.bright_yellow().bold()
            } else {
                |s: &str| s.bright_red().bold()
            }
        };

        match self {
            VrsError::Nom { error } => {
                writeln!(f, "      |  {} NOM ERROR!!!!!!", error)
            }
            VrsError::Error {
                message,
                hint,
                location,
            } => {
                let typ = applycolor(false)("error");
                Self::fmthdr(f, typ, location, message)?;
                Self::fmtctx(f, false, location, hint.as_ref())
            }
            VrsError::Warning {
                message,
                hint,
                location,
            } => {
                let typ = applycolor(true)("warning");
                Self::fmthdr(f, typ, location, message)?;
                Self::fmtctx(f, true, location, hint.as_ref())
            }
            VrsError::DoubleDef {
                ident,
                current,
                previous,
            } => {
                let typ = applycolor(false)("error");
                let message = format!("duplicate definition with name {}", ident);
                let hint = String::from("the second definition is here");
                Self::fmthdr(f, typ, current, &message)?;
                Self::fmtctx(f, false, current, Some(&hint))?;
                Self::fmtloc(f, previous)?;
                let hint = String::from("the previous definition was here");
                Self::fmtctx(f, false, previous, Some(&hint))
            }
            VrsError::ExpectedToken { location, tokens } => {
                let typ = applycolor(false)("error");
                let message = format!("unexpected token encounteted: {}", location);
                let hint = format!("expected one of {:?}", tokens);
                Self::fmthdr(f, typ, location, &message)?;
                Self::fmtctx(f, false, location, Some(&hint))
            }
            VrsError::Stack {
                message,
                location: l,
                next,
            } => {
                write!(f, "{}", next)?;
                writeln!(f, "      {}", pipe)?;
                return writeln!(
                    f,
                    "      {} {} {}:{}:{}",
                    pipe,
                    message,
                    l.context(),
                    l.line(),
                    l.column()
                );
            }
        }
    }
}

/// Implementation of [std::fmt::Debug] for [VrsError]
impl<I: ErrorLocation + fmt::Display> fmt::Debug for VrsError<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Implementation of [non::error::ContextError] for VrsError<I>
impl<I: ErrorLocation + fmt::Display> ContextError<I> for VrsError<I> {
    /// Creates a new error from an input position, a static string and an existing error.
    ///
    /// This is used mainly in the context combinator, to add user friendly information
    /// to errors when backtracking through a parse tree
    fn add_context(_input: I, _ctx: &'static str, _other: Self) -> Self {
        panic!("adding context");
    }
}

/// Implementation of [nom:error::ParseError] for VrsError<I>
impl<I: ErrorLocation + fmt::Display> ParseError<I> for VrsError<I> {
    /// Creates an error from the input position and an ErrorKind
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        VrsError::Nom {
            error: Error::new(input, kind),
        }
    }

    /// Combines the existing error with a new one created at position
    fn append(input: I, kind: ErrorKind, _other: Self) -> Self {
        VrsError::from_error_kind(input, kind)
    }

    fn or(self, other: Self) -> Self {
        match (self, other) {
            (
                VrsError::ExpectedToken {
                    location,
                    tokens: mut t1,
                },
                VrsError::ExpectedToken {
                    location: _,
                    tokens: mut t2,
                },
            ) => {
                t1.append(&mut t2);
                VrsError::ExpectedToken {
                    location,
                    tokens: t1,
                }
            }
            (s, _) => s,
        }
    }
}

/// Implementation of [nom::FromExternalError] for [VrsError]
impl<I: ErrorLocation + fmt::Display, E> FromExternalError<I, E> for VrsError<I> {
    fn from_external_error(input: I, kind: ErrorKind, _e: E) -> Self {
        VrsError::from_error_kind(input, kind)
    }
}

/// Implementation of [std::convert::From] for [VrsError]
///
/// This converts from a nom error to a VrsError.
impl<I: ErrorLocation + fmt::Display> From<Err<nom::error::Error<I>>> for VrsError<I> {
    fn from(e: nom::Err<nom::error::Error<I>>) -> Self {
        match e {
            nom::Err::Failure(e) => VrsError::from_error_kind(e.input, e.code),
            nom::Err::Error(e) => VrsError::from_error_kind(e.input, e.code),
            _ => panic!("shoudl nto happend..."),
        }
    }
}
