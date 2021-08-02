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

//! A Symboltable Implementation

// the used std library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// the used library internal functionality
use crate::ast::AstError;
use crate::ast::Type;
use crate::error::ErrorLocation;
use crate::token::TokenStream;

/// represents the kind of a symbol
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum SymbolKind {
    /// this symbol is a constant definition
    Const,
    /// this symbol is a function
    Function,
    /// this symbol is a parameter to a function
    Parameter,
    /// this symbol is a locally defined variable
    Variable,
    /// this is a special symbol referring to the state
    State,
    /// this is a special symbol referring to the interface
    Interface,
}

/// represents a defined symbol
#[derive(Clone)]
pub struct Symbol {
    /// the kind of the symbol, constant, function, ...
    pub kind: SymbolKind,
    /// the name of the symbol, its identifier
    pub name: String,
    /// the type of the symbol, `int|bool|...`
    pub typeinfo: Type,
    /// the location where this symbol has been defined
    pub loc: TokenStream,
}

/// Implementation of [Symbol]
impl Symbol {
    /// creates a new symbol from the given context and name, type
    pub fn new(ctxt: &str, name: &str, typeinfo: Type, kind: SymbolKind, loc: TokenStream) -> Self {
        let name = if ctxt.is_empty() {
            String::from(name)
        } else {
            format!("{}.{}", ctxt, name)
        };

        Symbol {
            kind,
            name,
            typeinfo,
            loc,
        }
    }

    /// returns true if the symbol ist constant
    pub fn is_const(&self) -> bool {
        matches!(&self.kind, SymbolKind::Const)
    }
}

/// Implementation of the [Display] trait for [Symbol]
///
/// We display it as a table form kind|type|name
impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(
            f,
            "{:10?}    {:9?}    {:20}    {}:{}:{}",
            self.kind,
            self.typeinfo,
            self.name,
            self.loc.context(),
            self.loc.column(),
            self.loc.line()
        )
    }
}

/// Implementation of the [Debug] trait for [Symbol]
impl Debug for Symbol {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(self, f)
    }
}

/// Represents a symbol table
pub struct SymbolTable {
    /// the symbols of the table
    syms: HashMap<String, Symbol>,
    /// represents local symbols
    localsyms: HashMap<String, Symbol>,
    /// the currenct context
    ctxt: String,
}

/// Implementation of [SymbolTable]
impl SymbolTable {
    /// creates a new empty symbol table
    pub fn new() -> Self {
        let syms = HashMap::new();
        let localsyms = HashMap::new();
        // insert the well-known symbols ?

        SymbolTable {
            syms,
            localsyms,
            ctxt: String::new(),
        }
    }

    /// tries to insert a symbol into the symbol table
    pub fn insert(&mut self, sym: Symbol) -> Result<Option<Symbol>, AstError> {
        let name = sym.name.clone();
        Ok(self.syms.insert(name, sym))
    }

    /// checks if there is a corresponding entry in the table
    pub fn contains(&self, sym: &str) -> bool {
        self.syms.contains_key(sym) || self.localsyms.contains_key(sym)
    }

    /// tries to obtain the entry
    pub fn get(&self, sym: &str) -> Option<&Symbol> {
        self.localsyms
            .get(sym)
            .or_else(|| self.syms.get(sym))
            .or_else(|| {
                let sym = format!("{}.{}", self.ctxt, sym);
                self.localsyms.get(&sym).or_else(|| self.syms.get(&sym))
            })
    }

    /// removes a symbol from the table
    pub fn remove(&mut self, sym: &str) -> Result<Symbol, AstError> {
        match self.syms.remove(sym) {
            Some(e) => Ok(e),
            None => Err(AstError::SymTableNotExists),
        }
    }

    /// sets the current context, the enclusing unit
    pub fn set_context(&mut self, ctxt: &str) {
        self.ctxt.truncate(0);
        self.ctxt.push_str(ctxt);
    }

    /// clears the local symbols
    pub fn local_clear(&mut self) {
        self.localsyms.clear();
    }

    /// inserts a local symbol
    pub fn local_insert(&mut self, sym: Symbol) -> Result<(), AstError> {
        if self.contains(&sym.name) {
            Err(AstError::SymTabInsertExists)
        } else {
            let name = sym.name.clone();
            self.localsyms.insert(name, sym);
            Ok(())
        }
    }

    /// removes a symbol from the table
    pub fn local_remove(&mut self, sym: &str) -> Result<Symbol, AstError> {
        match self.localsyms.remove(sym) {
            Some(e) => Ok(e),
            None => Err(AstError::SymTableNotExists),
        }
    }

    // returns the number of symbols
    pub fn count(&self) -> usize {
        self.syms.len() + self.localsyms.len()
    }
}

/// Implementation of the [fmt::Display] trait for [Symbol]
impl Display for SymbolTable {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "Kind     Type       Name                    Loc")?;
        self.syms.values().fold(Ok(()), |result, s| {
            result.and_then(|_| write!(f, "{:?}", s))
        })
    }
}

/// Implementation of the [Debug] trait for [Symbol]
impl Debug for SymbolTable {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(self, f)
    }
}
