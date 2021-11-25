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
//!
//! # General Structure
//!
//! The symbol table provides a mechanisms to look up symbols by name. Each symbol lives
//! within a given context. The contexts form a hierarchical structure:
//!  `root -> unit -> methods -> blocks`
//!
//! When entering a new block (e.g., unit), a new context is created.
//! The context is then dropped again when leaving the block.

// the used std library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

// the used library internal functionality
use crate::ast::Type;
use crate::error::{ErrorLocation, VrsError};
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

/// Implementation of the [Display] trait for [Symbol]
///
/// We display it as a table form kind|type|name
impl Display for SymbolKind {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{:?}", self)
    }
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
    //pub ast_node: Option<Box<AstNodeGeneric>>,
}

/// Implementation of [Symbol]
impl Symbol {
    /// creates a new symbol from the given context and name, type
    pub fn new(name: String, typeinfo: Type, kind: SymbolKind, loc: TokenStream) -> Self {
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
        write!(
            f,
            "{:10}   {:9?}    {:20}    {}:{}:{}",
            self.kind.to_string(), // need to do this, to get it formatted properly??
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

/// repretents a symbol table context
struct SymbolTableContext {
    /// the symbols of the table, we use a vector
    syms: HashMap<String, Symbol>,
    /// the currenct context
    ctxt: String,
}

impl SymbolTableContext {
    /// tries to insert a new symbol into the context
    fn insert(&mut self, sym: Symbol) -> bool {
        match self.syms.get(&sym.name) {
            None => {
                self.syms.insert(sym.name.clone(), sym);
                true
            }
            Some(x) => {
                // ther was already such a symbol. Show an erryr
                VrsError::new_double(sym.name.clone(), sym.loc.clone(), x.loc.clone()).print();
                false
            }
        }
    }

    /// removes an entry from the context
    fn remove(&mut self, name: &str) -> Option<Symbol> {
        self.syms.remove(name)
    }

    /// lookup a symbol by its name
    fn lookup(&self, name: &str) -> Option<&Symbol> {
        self.syms.get(name)
    }

    /// checks if the context contains a given key
    fn contains(&self, name: &str) -> bool {
        self.lookup(name).is_some()
    }

    /// the number of symbols in the context
    fn count(&self) -> usize {
        self.syms.len()
    }
}

/// Implementation of the [fmt::Display] trait for [SymbolTableContext]
impl Display for SymbolTableContext {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "Context: {}", self.ctxt)?;
        writeln!(f, "Kind         Type       Name                    Loc")?;
        for c in self.syms.values() {
            writeln!(f, "{}", c)?;
        }
        Ok(())
    }
}

/// Represents a symbol table
pub struct SymbolTable {
    /// a vector of symbol table contexts
    syms: Vec<SymbolTableContext>,
}

/// Implementation of [SymbolTable]
impl SymbolTable {
    /// creates a new empty symbol table
    pub fn new() -> Self {
        let mut st = SymbolTable { syms: Vec::new() };
        st.create_context(String::from("root"));
        st
    }

    /// creates a new context within the symbol table
    pub fn create_context(&mut self, context: String) {
        self.syms.push(SymbolTableContext {
            syms: HashMap::new(),
            ctxt: context,
        })
    }

    /// drops the current active context
    pub fn drop_context(&mut self) {
        self.syms.pop();
    }

    /// tries to insert the symbol into the current context
    pub fn insert(&mut self, sym: Symbol) -> bool {
        match self.lookup(&sym.name) {
            None => {
                let ctxt = self.syms.last_mut().unwrap();
                ctxt.insert(sym)
            }
            Some(x) => {
                // not warning here...
                VrsError::new_double(sym.name.clone(), sym.loc.clone(), x.loc.clone()).print();

                false
            }
        }
    }

    /// checks if there is a corresponding entry in the table
    pub fn contains(&self, sym: &str) -> bool {
        for ctxt in &self.syms {
            if ctxt.contains(sym) {
                return true;
            }
        }
        false
    }

    /// tries to lookup a symbol by the name in all contexts
    pub fn lookup(&self, name: &str) -> Option<&Symbol> {
        let mut sym = None;
        for ctxt in &self.syms {
            sym = ctxt.lookup(name);
            if sym.is_some() {
                return sym;
            }
        }
        sym
    }

    /// lookup a symbol with a given kind
    pub fn lookup_with_kind(&self, name: &str, kind: &[SymbolKind]) -> Option<&Symbol> {
        match self.lookup(name) {
            None => None,
            Some(x) => {
                if kind.contains(&x.kind) {
                    Some(x)
                } else {
                    None
                }
            }
        }
    }

    /// removes a symbol from the current context
    pub fn remove(&mut self, sym: &str) -> Option<Symbol> {
        let ctxt = self.syms.last_mut().unwrap();
        ctxt.remove(sym)
    }

    /// the number of symbols in the context
    pub fn count(&self) -> usize {
        self.syms.iter().fold(0, |v, c| v + c.count())
    }
}

/// Implementation of the [fmt::Display] trait for [SymbolTable]
impl Display for SymbolTable {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        writeln!(f, "SYMBOL TABLE\n")?;
        for c in &self.syms {
            writeln!(f, "{}", c)?;
        }
        Ok(())
    }
}

/// Implementation of the [Debug] trait for [Symbol]
impl Debug for SymbolTable {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(self, f)
    }
}

/// the default implementation
impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}
