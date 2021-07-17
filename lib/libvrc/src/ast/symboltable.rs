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

use std::collections::HashMap;
use std::fmt;

use crate::ast::ast::Type;
use crate::ast::AstError;
use crate::lexer::sourcepos::SourcePos;

/// defines the type of the key
type SymbolKey = String;

/// represents the kind of a symbol
#[derive(Debug, Clone, Copy)]
enum SymbolKind {
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
}

/// represents a defined symbol
#[derive(Clone)]
struct Symbol {
    /// the kind of the symbol, constant, function, ...
    pub kind: SymbolKind,
    /// the name of the symbol, its identifier
    pub name: SymbolKey,
    /// the type of the symbol, `int|bool|...`
    pub typeinfo: Type,
    /// the position where this symbol has been defined
    pub pos: SourcePos,
}

/// Implementation of [Symbol]
impl Symbol {}

/// Implementation of the [fmt::Display] trait for [Symbol]
///
/// We display it as a table form kind|type|name
impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "{:10?}    {:9?}    {}",
            self.kind, self.typeinfo, self.name
        )
    }
}

/// Implementation of the [fmt::Debug] trait for [Symbol]
impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "{:10?}    {:9?}    {}    {}",
            self.kind, self.typeinfo, self.name, self.pos
        )
    }
}

/// Represents a symbol table
struct SymbolTable {
    /// represents the current context of the symbol table
    context: Vec<String>,
    /// the symbols of the table
    syms: HashMap<SymbolKey, Symbol>,
}

/// Implementation of [SymbolTable]
impl SymbolTable {
    /// creates a new empty symbol table
    pub fn new(context: String) -> Self {
        let syms = HashMap::new();
        let context = vec![context];
        // insert the well-known symbols ?

        SymbolTable { context, syms }
    }

    /// creates a new symbol table as a copy from [self]
    pub fn from_self(&self, subcontext: String) -> Self {
        let syms = self.syms.clone();
        let mut context = self.context.clone();
        context.push(subcontext);
        SymbolTable { context, syms }
    }

    /// tries to insert a symbol into the symbol table
    pub fn insert(&mut self, sym: Symbol) -> Result<(), AstError> {
        if self.contains(&sym.name) {
            Err(AstError::SymTabInsertExists)
        } else {
            let name = sym.name.clone();
            self.syms.insert(name, sym);
            Ok(())
        }
    }

    /// checks if there is a corresponding entry in the table
    pub fn contains(&self, sym: &SymbolKey) -> bool {
        self.syms.contains_key(sym)
    }

    /// tries to obtain the entry
    pub fn get(&self, sym: &SymbolKey) -> Option<&Symbol> {
        self.syms.get(sym)
    }

    /// removes a symbol from the table
    pub fn remove(&mut self, sym: &SymbolKey) -> Result<Symbol, AstError> {
        match self.syms.remove(sym) {
            Some(e) => Ok(e),
            None => Err(AstError::SymTableNotExists),
        }
    }
}

/// Implementation of the [fmt::Display] trait for [Symbol]
impl fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Kind          Type         Name")?;
        self.syms.values().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "{}", s))
        })
    }
}

/// Implementation of the [fmt::Debug] trait for [Symbol]
impl fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Kind          Type         Name")?;
        self.syms.values().fold(Ok(()), |result, s| {
            result.and_then(|_| writeln!(f, "{:?}", s))
        })
    }
}
