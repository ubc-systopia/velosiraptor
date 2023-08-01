// VelosiAst -- a Ast for the Velosiraptor Language
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

//! # VelosiAst -- The Ast for the Velosiraptor Language
//!
//! This module defines the AST of the langauge with its different AST nodes.

// used standard library functionality
use core::str::Split;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// used third party cartes

// used parse tree definitions
use velosiparser::{VelosiParseTreeIdentifier, VelosiTokenStream};

// used crate functionality

////////////////////////////////////////////////////////////////////////////////////////////////////
// Identifier
////////////////////////////////////////////////////////////////////////////////////////////////////

/// path separator for identifiers
pub const IDENT_PATH_SEP: &str = ".";

/// Represents an identifier in the AST
///
/// An identifier has two parts:
///  1) the identifier that is used within the context of the current scope (e.g., slice name)
///  2) a fully qualified path to the that includes the scope. (e.g., state.field.slice)
///
#[derive(Eq, Clone)]
pub struct VelosiAstIdentifier {
    /// the identifier
    pub ident: Rc<String>,
    /// fully qualified identifier
    pub path: Rc<String>,
    /// the location of the identifier in the source pos
    pub loc: VelosiTokenStream,
}

impl VelosiAstIdentifier {
    /// creates a new identifier from the give name, the prefix is empty
    pub fn new(name: String, loc: VelosiTokenStream) -> Self {
        Self::with_prefix("", name, loc)
    }

    /// creates a new identifier with the given prefix and name
    pub fn with_prefix(prefix: &str, name: String, loc: VelosiTokenStream) -> Self {
        let ident = Rc::new(name.clone());
        let path = if prefix.is_empty() {
            ident.clone()
        } else {
            let path = format!("{prefix}{IDENT_PATH_SEP}{name}");
            Rc::new(path)
        };

        Self { ident, path, loc }
    }

    /// convert the parse tree identifier to a ast identifier with the given prefix
    pub fn from_parse_tree_with_prefix(pt: VelosiParseTreeIdentifier, prefix: &str) -> Self {
        Self::with_prefix(prefix, pt.name, pt.loc)
    }

    pub fn extend(&mut self, other: Self) -> &mut Self {
        self.ident = Rc::new(format!("{}{}{}", self.ident, IDENT_PATH_SEP, other.ident));
        self.path = Rc::new(format!("{}{}{}", self.path, IDENT_PATH_SEP, other.path));
        self.loc.expand_until_end(&other.loc);
        self
    }

    pub fn extend_with_str(&mut self, slice: &str) -> &mut Self {
        self.ident = Rc::new(format!("{}{}{}", self.ident, IDENT_PATH_SEP, slice));
        self.path = Rc::new(format!("{}{}{}", self.path, IDENT_PATH_SEP, slice));
        self
    }

    /// obtains a reference to the identifier string
    pub fn ident(&self) -> &Rc<String> {
        &self.ident
    }

    /// return the identifier as a string slice
    pub fn as_str(&self) -> &str {
        self.ident.as_str()
    }

    /// obtains the path as a string
    pub fn path(&self) -> &Rc<String> {
        &self.path
    }

    pub fn path_split(&'_ self) -> Split<&'_ str> {
        self.path.split(IDENT_PATH_SEP)
    }
}

/// Conversion from a string slice to an AST identifier
impl From<&str> for VelosiAstIdentifier {
    fn from(id: &str) -> Self {
        Self::from(id.to_string())
    }
}

/// Conversion from a string to an AST identifier
impl From<String> for VelosiAstIdentifier {
    fn from(id: String) -> Self {
        Self::new(id, VelosiTokenStream::default())
    }
}

/// Conversion from a parse-tree identifier to an AST identifier
impl From<VelosiParseTreeIdentifier> for VelosiAstIdentifier {
    fn from(id: VelosiParseTreeIdentifier) -> Self {
        Self::new(id.name, id.loc)
    }
}

/// Implementation of the [Display] trait for [VelosiAstIdentifier]
impl Display for VelosiAstIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.path)
    }
}

/// Implementation of the [Display] trait for [VelosiAstIdentifier]
impl Debug for VelosiAstIdentifier {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self, f)
    }
}

/// Implementation of [PartialEq] for [VelosiAstIdentifier]
///
/// Two identifiers are equal if their respective fully qualified paths
/// are equal.
impl PartialEq for VelosiAstIdentifier {
    fn eq(&self, other: &Self) -> bool {
        self.path.eq(&other.path)
    }
}

/// Implementation of [PartialOrd] for [VelosiAstIdentifier]
impl PartialOrd for VelosiAstIdentifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Implementation of [Ord] for [VelosiAstIdentifier]
///
/// We implement our own variant of ordering that considers only the path,
/// i.e., the fully qualified identifier in the ordering of the two identifiers.
impl Ord for VelosiAstIdentifier {
    fn cmp(&self, other: &Self) -> Ordering {
        self.path.as_ref().cmp(other.path.as_ref())
    }
}

/// Implementation of [Hash] for [VelosiAstIdentifier]
///
/// We implement our own variant of hash as we do not want to consider the
/// location of the expression when comparing two expressions. Moreover,
/// we only hash the path as this is the fully qualified identifier.
impl Hash for VelosiAstIdentifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.path.as_ref().hash(state);
    }
}
