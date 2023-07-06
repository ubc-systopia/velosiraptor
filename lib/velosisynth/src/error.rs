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
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::ops::Add;

// external dependencies
use colored::*;

use velosiast::VelosiTokenStream;

fn print_location_line(f: &mut Formatter<'_>, tokstream: &VelosiTokenStream) -> FmtResult {
    let blue = |s: &str| s.bold().blue();
    let pipe = blue("|");

    // location information
    let location = tokstream.span();
    writeln!(f, "     {} {}", blue("-->"), location.loc())?;
    writeln!(f, "      {pipe}")
}

fn print_location_context(
    f: &mut Formatter<'_>,
    warn: bool,
    tokstream: &VelosiTokenStream,
) -> FmtResult {
    let blue = |s: &str| s.bold().blue();
    let highlight = if warn {
        |s: &str| s.bold().bright_yellow()
    } else {
        |s: &str| s.bold().bright_red()
    };

    let pipe = blue("|");

    let location = tokstream.span();

    let linenum = location.line().to_string();

    let linectxt = location.srcline();

    if linectxt.len() <= 100 {
        // calculate the indentation
        let col = location.column();
        let indent = (0..col - 1).map(|_| " ").collect::<String>();

        // get the underline
        let ulen = std::cmp::min(location.len(), linectxt.len() - indent.len());
        let underline = (0..ulen).map(|_| "^").collect::<String>();

        // the line context with highligted part that is wrong
        writeln!(f, " {:>4} {}  {}", blue(&linenum), pipe, linectxt)?;
        write!(f, "      {}  {}{}", pipe, indent, highlight(&underline))
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

        let ulen = std::cmp::min(
            location.len(),
            printrange.end - printrange.start - indent.len(),
        );
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
            highlight(&underline),
        )
    }
}

fn print_location(f: &mut Formatter<'_>, warn: bool, tokstream: &VelosiTokenStream) -> FmtResult {
    print_location_line(f, tokstream)?;
    print_location_context(f, warn, tokstream)
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Custom Error with Builder
///////////////////////////////////////////////////////////////////////////////////////////////////

pub(crate) struct VelosiSynthErrorBuilder {
    warn: bool,
    message: String,
    hint: Option<String>,
    tokstream: Option<VelosiTokenStream>,
    related: Vec<(String, VelosiTokenStream)>,
}

impl VelosiSynthErrorBuilder {
    pub fn warn(message: String) -> Self {
        Self {
            warn: true,
            message,
            hint: None,
            tokstream: None,
            related: Vec::new(),
        }
    }

    pub fn err(message: String) -> Self {
        Self {
            warn: false,
            message,
            hint: None,
            tokstream: None,
            related: Vec::new(),
        }
    }

    /// Adds a hint to the error message
    pub fn add_hint(&mut self, hint: String) -> &mut Self {
        self.hint = Some(hint);
        self
    }

    /// Adds a location to the error information
    pub fn add_location(&mut self, tokstream: VelosiTokenStream) -> &mut Self {
        self.tokstream = Some(tokstream);
        self
    }

    // pub fn add_related_location(
    //     &mut self,
    //     message: String,
    //     tokstream: VelosiTokenStream,
    // ) -> &mut Self {
    //     self.related.push((message, tokstream));
    //     self
    // }

    pub fn build(&mut self) -> VelosiSynthError {
        if self.hint.is_none() && self.tokstream.is_none() && !self.related.is_empty() {
            let (message, tokstream) = self.related.pop().unwrap();
            self.hint = Some(message);
            self.tokstream = Some(tokstream);
        }

        VelosiSynthError::Custom(VelosiSynthErrorCustom {
            message: self.message.clone(),
            warn: self.warn,
            hint: self.hint.take(),
            tokstream: self.tokstream.take().unwrap_or_default(),
            related: self.related.drain(..).collect(),
        })
    }
}

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub struct VelosiSynthErrorCustom {
    /// error message
    message: String,
    /// whether this is an error or a warning
    warn: bool,
    /// Hint
    hint: Option<String>,
    /// the location where the error happened
    tokstream: VelosiTokenStream,
    /// related locations in the error
    related: Vec<(String, VelosiTokenStream)>,
}

impl From<VelosiSynthErrorCustom> for VelosiSynthIssues {
    fn from(err: VelosiSynthErrorCustom) -> Self {
        let mut issues = Self::new();
        issues.push(VelosiSynthError::Custom(err));
        issues
    }
}

/// Implementation of [Display] for [VelosiSynthErrorCustom]
impl Display for VelosiSynthErrorCustom {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // closure for coloring
        let highlight = if self.warn {
            |s: &str| s.bold().bright_yellow()
        } else {
            |s: &str| s.bold().bright_red()
        };

        let blue = |s: &str| s.bold().blue();
        let pipe = blue("|");

        // the error message
        if self.warn {
            writeln!(
                f,
                "{}{} {}",
                highlight("warning"),
                ":".bold(),
                self.message.bold()
            )?;
        } else {
            writeln!(
                f,
                "{}{} {}",
                highlight("error"),
                ":".bold(),
                self.message.bold()
            )?;
        }

        // the location, if it is set
        if !self.tokstream.span().is_default() {
            print_location(f, self.warn, &self.tokstream)?;
        }

        // apply the hint if needed
        match &self.hint {
            Some(h) => writeln!(f, " {}", highlight(h.as_str()))?,
            None => writeln!(f)?,
        }

        if !self.related.is_empty() {
            writeln!(f, "   {}", blue("..."))?;
            writeln!(f, "      {pipe}")?;
        }

        for (message, tokstream) in &self.related {
            print_location_context(f, self.warn, tokstream)?;
            writeln!(f, " {}", highlight(message.as_str()))?;
        }
        Ok(())
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Unsat Defined Symbols
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiSynthErrorUnsatDef {
    /// message of the unsat error
    message: String,
    /// the location of the first definition
    locs: Vec<VelosiTokenStream>,
}

impl VelosiSynthErrorUnsatDef {
    pub fn new(message: String, locs: Vec<VelosiTokenStream>) -> Self {
        Self { message, locs }
    }

    pub fn push_loc(&mut self, loc: VelosiTokenStream) -> &mut Self {
        self.locs.push(loc);
        self
    }
}

impl From<VelosiSynthErrorUnsatDef> for VelosiSynthError {
    fn from(err: VelosiSynthErrorUnsatDef) -> Self {
        VelosiSynthError::UnsatDef(err)
    }
}

impl Display for VelosiSynthErrorUnsatDef {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();
        let blue = |s: &str| s.bold().blue();

        // the error message
        writeln!(
            f,
            "{}{} {}",
            red("error"),
            ":".bold(),
            self.message.as_str().bold()
        )?;

        let pipe = blue("|");

        match self.locs.len() {
            0 => {}
            1 => {
                // location information
                writeln!(f, "     {} {}", blue("-->"), self.locs[0].loc())?;
                writeln!(f, "      {pipe}")?;
                print_location_context(f, false, &self.locs[0])?;
                writeln!(f, " {}", red("this expression cannot be satisfied"))?;
            }
            2 => {
                // location information
                writeln!(f, "     {} {}", blue("-->"), self.locs[0].loc())?;
                writeln!(f, "      {pipe}")?;
                print_location_context(f, false, &self.locs[0])?;
                writeln!(
                    f,
                    " {}",
                    red("this expression conflicts with another expression")
                )?;

                writeln!(f, "   {}", blue("..."))?;
                writeln!(f, "      {pipe}")?;

                print_location_context(f, false, &self.locs[1])?;
                writeln!(f, " {}", red("this is the conflicting expression"))?;
            }
            _l => {
                writeln!(f, "     {} {}", blue("-->"), self.locs[0].loc())?;
                writeln!(
                    f,
                    "      {}",
                    blue("---------- begin expression group -----------")
                )?;
                writeln!(f, "      {pipe}")?;

                for (i, loc) in self.locs.iter().enumerate() {
                    print_location_context(f, false, loc)?;
                    let msg = format!(
                        "this is conflicting expression #{}/{}",
                        i + 1,
                        self.locs.len()
                    );
                    writeln!(f, " {}", red(&msg))?;
                }
                writeln!(
                    f,
                    "      {}",
                    blue("----------- end expression group ------------")
                )?;
            }
        }
        Ok(())
    }
}

impl From<VelosiSynthErrorUnsatDef> for VelosiSynthIssues {
    fn from(err: VelosiSynthErrorUnsatDef) -> Self {
        let mut issues = Self::new();
        issues.push(VelosiSynthError::UnsatDef(err));
        issues
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Synthesis Errors
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub enum VelosiSynthError {
    UnsatDef(VelosiSynthErrorUnsatDef),
    Custom(VelosiSynthErrorCustom),
}

impl VelosiSynthError {
    pub fn is_warn(&self) -> bool {
        match self {
            VelosiSynthError::Custom(err) => err.warn,
            _ => false,
        }
    }
}

/// Implementation of [Display] for [VelosiSynthError]
impl Display for VelosiSynthError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            VelosiSynthError::UnsatDef(e) => e.fmt(f),
            VelosiSynthError::Custom(e) => e.fmt(f),
        }
    }
}

impl From<VelosiSynthError> for VelosiSynthIssues {
    fn from(err: VelosiSynthError) -> Self {
        let mut issues = Self::new();
        issues.push(err);
        issues
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Ast Issues
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiSynthIssues {
    errors: Vec<VelosiSynthError>,
    num_errors: usize,
    num_warnings: usize,
}

impl VelosiSynthIssues {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            num_errors: 0,
            num_warnings: 0,
        }
    }

    pub fn has_errors(&self) -> bool {
        self.num_errors > 0
    }

    pub fn has_warnings(&self) -> bool {
        self.num_warnings > 0
    }

    pub fn is_ok(&self) -> bool {
        self.num_errors == 0 && self.num_warnings == 0
    }

    pub fn push(&mut self, issue: VelosiSynthError) {
        if issue.is_warn() {
            self.num_warnings += 1;
        } else {
            self.num_errors += 1;
        }
        self.errors.push(issue);
    }

    pub fn merge(&mut self, other: VelosiSynthIssues) {
        self.num_errors += other.num_errors;
        self.num_warnings += other.num_warnings;
        self.errors.extend(other.errors);
    }

    pub fn merge_result<T>(&mut self, other: Result<T, VelosiSynthIssues>) {
        match other {
            Ok(_) => {}
            Err(issues) => self.merge(issues),
        }
    }
}

impl Default for VelosiSynthIssues {
    fn default() -> Self {
        Self::new()
    }
}

impl Add for VelosiSynthIssues {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        self.errors.extend(other.errors);
        Self {
            errors: self.errors,
            num_errors: self.num_errors + other.num_errors,
            num_warnings: self.num_warnings + other.num_warnings,
        }
    }
}

/// Implementation of [Display] for [VelosiSynthIssues]
impl Display for VelosiSynthIssues {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for e in &self.errors {
            Display::fmt(e, f)?;
        }

        let red = |s: &str| s.bright_red().bold();
        let yellow = |s: &str| s.bright_yellow().bold();
        if self.num_warnings > 0 {
            writeln!(
                f,
                "{}{} generated {} warnings",
                yellow("warning"),
                ":".bold(),
                self.num_warnings
            )?;
        }

        if self.num_errors > 0 {
            writeln!(
                f,
                "{}{} could not compile due to {} previous errors; {} warnings emitted",
                red("error"),
                ":".bold(),
                self.num_errors,
                self.num_warnings
            )?;
        }

        Ok(())
    }
}
