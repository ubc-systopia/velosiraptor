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

use std::fmt;
use colored::*;

// get the NOM traits
use nom::error::{ContextError, ErrorKind, FromExternalError, ParseError};
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
pub struct VrsError<I: ErrorLocation> {
    /// the type of this error
    etype: ErrorType,
    /// error message
    message: String,
    /// Hint
    hint: Option<String>,
    /// the location where the error happened
    location: I,
    /// represents a path leading to the error e.g., file -> unit -> method
    path: Option<Box<VrsError<I>>>,
}

/// Implementation of the VrsError
impl<I: ErrorLocation> VrsError<I> {
    /// creates a new VrsError struct as ErrorType::Error
    pub fn new(location: I, message: String) -> Self {
        VrsError {
            etype: ErrorType::Error,
            message,
            hint: None,
            location,
            path: None,
        }
    }
    /// creates a new VrsError struct as ErrorType::Error from a &str
    pub fn from_str(location: I, message: &str) -> Self {
        VrsError::new(location, message.to_string())
    }

    /// creates a new VrsError struct as ErrorType::Error from a &str
    pub fn from_nom(e: nom::Err<nom::error::Error<I>>, message: &str) -> Self {
        match e {
            nom::Err::Failure(e) => VrsError::from_str(e.input, message),
            _ => panic!("shoudl not happend..."),
        }
    }

    /// adds a hint to this error
    pub fn add_hint(&mut self, hint: String) {
        self.hint = Some(hint);
    }
    /// sets the errory type for this error
    pub fn set_type(&mut self, etype: ErrorType) {
        self.etype = etype;
    }
}


/// Implementation of [std::fmt::Display] for [VrsError]
impl<I: ErrorLocation> fmt::Display for VrsError<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let es = match self.etype {
            ErrorType::Error => "error".bright_red().bold(),
            ErrorType::Warning => "error".bright_yellow().bold(),
        };

        writeln!(
            f,
            "{}{} {}",
            es,
            ":".bold(),
            self.message.bold()
        )?;

        writeln!(
            f,
            "     {} {}:{}:{}",
            "-->".bold().blue(),
            self.location.context(),
            self.location.column(),
            self.location.line()
        )?;

        match &self.path {
            Some(p) => {
                writeln!(f, "      | {}", self.message)?;
                writeln!(f, "{}", p)
            }
            None => {
                // --> src/error/mod.rs:112:62
                writeln!(f, "      {}", "|".bold().blue())?;
                // // the line context
                writeln!(
                    f,
                    "      {}         {}",
                    "|".bold().blue(),
                    self.location.linecontext()
                )?;
                // // the error message
                write!(
                    f,
                    "      {}         {}{} ",
                    "|".bold().blue(),
                    (0..self.location.column() - 1)
                        .map(|_| " ")
                        .collect::<String>(),
                    (0..self.location.length())
                        .map(|_| "^")
                        .collect::<String>()
                        .as_str()
                        .bold()
                        .red(),
                )?;
                match &self.hint {
                    Some(e) => writeln!(f, "{}", e.as_str().bold().red()),
                    None => writeln!(f, ""),
                }
            }
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
        VrsError {
            etype: ErrorType::Error,
            message: ctx.to_string(),
            hint: None,
            location: input,
            path: Some(Box::new(other)),
        }
    }
}

/// Implementation of [nom:error::ParseError] for VrsError<I>
impl<I: ErrorLocation> ParseError<I> for VrsError<I> {
    /// Creates an error from the input position and an ErrorKind
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        match kind {
            ErrorKind::Tag => VrsError::new(input, "Unexpected token".to_string()),
            ErrorKind::TakeUntil => VrsError::new(input, "Unexpected end of file".to_string()),
            ErrorKind::Eof => VrsError::new(input, "Unexpected end of file".to_string()),
            _ => VrsError::new(input, "Unknown error kind.".to_string()),
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
            _ => panic!("shoudl nto happend..."),
        }
    }
}
