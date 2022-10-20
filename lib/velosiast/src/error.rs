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
use std::ops::Add;
use std::rc::Rc;

// external dependencies
use colored::*;

use crate::ast::VelosiAstIdentifier;
use crate::VelosiTokenStream;

fn print_location_line(f: &mut Formatter<'_>, tokstream: &VelosiTokenStream) -> Result {
    let blue = |s: &str| s.bold().blue();
    let pipe = blue("|");

    // location information
    let location = tokstream.span();
    writeln!(f, "     {} {}", blue("-->"), location.loc())?;
    writeln!(f, "      {}", pipe)
}

fn print_location_context(
    f: &mut Formatter<'_>,
    warn: bool,
    tokstream: &VelosiTokenStream,
) -> Result {
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

fn print_location(f: &mut Formatter<'_>, warn: bool, tokstream: &VelosiTokenStream) -> Result {
    print_location_line(f, tokstream)?;
    print_location_context(f, warn, tokstream)
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Custom Error with Builder
///////////////////////////////////////////////////////////////////////////////////////////////////

pub(crate) struct VelosiAstErrBuilder {
    warn: bool,
    message: String,
    hint: Option<String>,
    tokstream: Option<VelosiTokenStream>,
    related: Vec<(String, VelosiTokenStream)>,
}

impl VelosiAstErrBuilder {
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

    pub fn add_related_location(
        &mut self,
        message: String,
        tokstream: VelosiTokenStream,
    ) -> &mut Self {
        self.related.push((message, tokstream));
        self
    }

    pub fn build(&mut self) -> VelosiAstErr {
        if self.hint.is_none() && self.tokstream.is_none() && !self.related.is_empty() {
            let (message, tokstream) = self.related.pop().unwrap();
            self.hint = Some(message);
            self.tokstream = Some(tokstream);
        }

        VelosiAstErr::Custom(VelosiAstErrCustom {
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
pub struct VelosiAstErrCustom {
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

/// Implementation of [Display] for [VelosiAstErrCustom]
impl Display for VelosiAstErrCustom {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
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
            writeln!(f, "      {}", pipe)?;
        }

        for (message, tokstream) in &self.related {
            print_location_context(f, self.warn, tokstream)?;
            writeln!(f, " {}", highlight(message.as_str()))?;
        }
        Ok(())
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Double Defined Symbols
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiAstErrDoubleDef {
    /// the name of the double defined variable
    name: Rc<String>,
    /// the location of the first definition
    first: VelosiTokenStream,
    /// the location of the second definition
    second: VelosiTokenStream,
}

impl VelosiAstErrDoubleDef {
    pub fn new(name: Rc<String>, first: VelosiTokenStream, second: VelosiTokenStream) -> Self {
        Self {
            name,
            first,
            second,
        }
    }
}

impl From<VelosiAstErrDoubleDef> for VelosiAstErr {
    fn from(err: VelosiAstErrDoubleDef) -> Self {
        VelosiAstErr::DoubleDef(err)
    }
}

impl Display for VelosiAstErrDoubleDef {
    fn fmt(&self, f: &mut Formatter) -> Result {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();
        let blue = |s: &str| s.bold().blue();

        // the error message
        let msg = format!("duplicate definitions with name `{}`", self.name);
        writeln!(f, "{}{} {}", red("error"), ":".bold(), msg.bold())?;

        let pipe = blue("|");

        // location information
        writeln!(f, "     {} {}", blue("-->"), self.second.loc())?;
        writeln!(f, "      {}", pipe)?;

        print_location_context(f, false, &self.first)?;
        let m = format!("previous definition of `{}` was here", self.name);
        writeln!(f, " {}", red(m.as_str()))?;
        writeln!(f, "   {}", blue("..."))?;
        writeln!(f, "      {}", pipe)?;
        print_location_context(f, false, &self.second)?;
        writeln!(f, " {}", red("duplicate definition"))

        //         error[E0201]: duplicate definitions with name `new`:
        //    --> lib/velosiast/src/error.rs:216:5
        //     |
        // 209 |     pub fn new(name: Rc<String>, first: VelosiTokenStream, second: VelosiTokenStream) -> Self {
        //     |     ----------------------------------------------------------------------------------------- previous definition of `new` here
        // ...
        // 216 |     pub fn new() {}
        //     |     ^^^^^^^^^^^^ duplicate definition
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Undefined symbols
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiAstErrUndef {
    /// the name of the undefined identifier
    name: Rc<String>,
    /// the location of the undefined identifier occurrance
    loc: VelosiTokenStream,
    /// if set, the location of the symbol of different type
    other: Option<VelosiTokenStream>,
}

impl VelosiAstErrUndef {
    pub fn new(name: Rc<String>, loc: VelosiTokenStream) -> Self {
        Self {
            name,
            loc,
            other: None,
        }
    }

    pub fn with_other(name: Rc<String>, loc: VelosiTokenStream, other: VelosiTokenStream) -> Self {
        Self {
            name,
            loc,
            other: Some(other),
        }
    }

    pub fn from_ident(id: &VelosiAstIdentifier) -> Self {
        Self::new(id.name.clone(), id.loc.clone())
    }

    pub fn from_ident_with_other(id: &VelosiAstIdentifier, other: VelosiTokenStream) -> Self {
        Self::with_other(id.name.clone(), id.loc.clone(), other)
    }
}

impl From<VelosiAstErrUndef> for VelosiAstErr {
    fn from(err: VelosiAstErrUndef) -> Self {
        VelosiAstErr::Undefined(err)
    }
}

impl Display for VelosiAstErrUndef {
    fn fmt(&self, f: &mut Formatter) -> Result {
        // closure for coloring
        let red = |s: &str| s.bright_red().bold();

        // the error message
        let m = if self.other.is_some() {
            format!(
                "symbol named `{}` was defined with a different kind",
                self.name
            )
        } else {
            format!("no symbol named `{}` found in the current scope", self.name)
        };

        writeln!(f, "{}{} {}", red("error"), ":".bold(), m.bold())?;

        // the location, if it is set
        if !self.loc.span().is_default() {
            print_location(f, false, &self.loc)?;
        }

        if let Some(other) = &self.other {
            let m = "this is the symbol with the wrong kind";
            writeln!(f, " {}", red(m))?;
            print_location(f, false, other)?;
            writeln!(f, " {}", red("symbol was defined here"))
        } else {
            writeln!(f, " {}", red("not found in this scope"))
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Ast Errors
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Defines a Lexer Error
#[derive(PartialEq, Eq, Debug)]
pub enum VelosiAstErr {
    DoubleDef(VelosiAstErrDoubleDef),
    Undefined(VelosiAstErrUndef),
    Custom(VelosiAstErrCustom),
}

impl VelosiAstErr {
    pub fn is_warn(&self) -> bool {
        match self {
            VelosiAstErr::Custom(err) => err.warn,
            _ => false,
        }
    }
}

/// Implementation of [Display] for [VelosiAstErr]
impl Display for VelosiAstErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            VelosiAstErr::DoubleDef(e) => e.fmt(f),
            VelosiAstErr::Custom(e) => e.fmt(f),
            VelosiAstErr::Undefined(e) => e.fmt(f),
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Ast Issues
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub struct VelosiAstIssues {
    errors: Vec<VelosiAstErr>,
    num_errors: usize,
    num_warnings: usize,
}

impl VelosiAstIssues {
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

    pub fn push(&mut self, issue: VelosiAstErr) {
        if issue.is_warn() {
            self.num_warnings += 1;
        } else {
            self.num_errors += 1;
        }
        self.errors.push(issue);
    }

    pub fn merge(&mut self, other: VelosiAstIssues) {
        self.num_errors += other.num_errors;
        self.num_warnings += other.num_warnings;
        self.errors.extend(other.errors);
    }
}

impl Default for VelosiAstIssues {
    fn default() -> Self {
        Self::new()
    }
}

impl Add for VelosiAstIssues {
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

impl From<VelosiAstErr> for VelosiAstIssues {
    fn from(err: VelosiAstErr) -> Self {
        let mut issues = Self::new();
        issues.push(err);
        issues
    }
}

impl From<VelosiAstErrUndef> for VelosiAstIssues {
    fn from(err: VelosiAstErrUndef) -> Self {
        let mut issues = Self::new();
        issues.push(VelosiAstErr::Undefined(err));
        issues
    }
}

/// Implementation of [Display] for [VelosiAstIssues]
impl Display for VelosiAstIssues {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
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
                "{}{} could not compile due to {} previous errors; {} warnigns emitted",
                red("error"),
                ":".bold(),
                self.num_errors,
                self.num_warnings
            )?;
        }

        Ok(())
    }
}
