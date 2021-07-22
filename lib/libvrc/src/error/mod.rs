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

/// represents an error type
#[derive(PartialEq)]
pub enum ErrorType {
    /// this is an error
    Error,
    /// this is a warning
    Warning,
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
    /// represents a custom error
    Error {
        /// error message
        message: String,
        /// Hint
        hint: Option<String>,
        /// the location where the error happened
        location: I,
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
impl<I: ErrorLocation> VrsError<I> {
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

    pub fn stack(location: I, message: String, other: VrsError<I>) -> Self {
        VrsError::Stack {
            message,
            location,
            next: Box::new(other),
        }
    }

    pub fn print(&self) {
        eprintln!("{}", self)
    }
}

/// Implementation of [std::fmt::Display] for [VrsError]
impl<I: ErrorLocation> fmt::Display for VrsError<I> {
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

        let (typ, msg, hint, loc, color) = match self {
            VrsError::Nom { error: _ } => {
                return writeln!(f, "      | NOM ERROR!!!!!!");
            }
            VrsError::Error {
                message,
                hint,
                location,
            } => {
                let typ = applycolor(false)("error");
                (typ, message, hint, location, applycolor(false))
            }
            VrsError::Warning {
                message,
                hint,
                location,
            } => {
                let typ = applycolor(true)("warning");
                (typ, message, hint, location, applycolor(true))
            }
            VrsError::Stack {
                message,
                location: _,
                next,
            } => {
                writeln!(f, "{}", next)?;
                writeln!(f, "      {}", pipe)?;
                return writeln!(f, "      | {}", message);
            }
        };

        let line = loc.line();
        let lineblue = line.to_string().as_str().bold().blue();
        let col = loc.column();
        let ctxt = loc.context();
        let linectxt = loc.linecontext();

        let indent = (0..col - 1).map(|_| " ").collect::<String>();
        let underline = (0..loc.length())
            .map(|_| "^")
            .collect::<String>()
            .as_str()
            .bold()
            .red();

        // error: <message>
        writeln!(f, "{}{} {}", typ, ":".bold(), msg.bold())?;
        // --> src/error/mod.rs:112:62
        writeln!(f, "     {} {}:{}:{}", "-->".bold().blue(), ctxt, line, col)?;

        // // the line context
        writeln!(f, " {:>4} {}         {}", lineblue, pipe, linectxt)?;

        // // the error message
        write!(f, "      {}         {}{}", pipe, indent, underline)?;
        match hint {
            Some(e) => writeln!(f, " {}{}", color("hint: "), color(e)),
            None => writeln!(f, ""),
        }
    }
}

/// Implementation of [std::fmt::Debug] for [VrsError]
impl<I: ErrorLocation> fmt::Debug for VrsError<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Implementation of [non::error::ContextError] for VrsError<I>
impl<I: ErrorLocation> ContextError<I> for VrsError<I> {
    /// Creates a new error from an input position, a static string and an existing error.
    ///
    /// This is used mainly in the context combinator, to add user friendly information
    /// to errors when backtracking through a parse tree
    fn add_context(input: I, ctx: &'static str, other: Self) -> Self {
        VrsError::stack(input, ctx.to_string(), other)
    }
}

/// Implementation of [nom:error::ParseError] for VrsError<I>
impl<I: ErrorLocation> ParseError<I> for VrsError<I> {
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
}

/// Implementation of [nom::FromExternalError] for [VrsError]
impl<I: ErrorLocation, E> FromExternalError<I, E> for VrsError<I> {
    fn from_external_error(input: I, kind: ErrorKind, e: E) -> Self {
        VrsError::from_error_kind(input, kind)
    }
}

/// Implementation of [std::convert::From] for [VrsError]
///
/// This converts from a nom error to a VrsError.
impl<I: ErrorLocation> From<Err<nom::error::Error<I>>> for VrsError<I> {
    fn from(e: nom::Err<nom::error::Error<I>>) -> Self {
        match e {
            nom::Err::Failure(e) => VrsError::from_error_kind(e.input, e.code),
            nom::Err::Error(e) => VrsError::from_error_kind(e.input, e.code),
            _ => panic!("shoudl nto happend..."),
        }
    }
}
