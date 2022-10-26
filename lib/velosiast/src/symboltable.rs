// VelosiAst -- a ast for the Velosiraptor Language
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

// the used std library functionality
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

// the used library internal functionality
use crate::ast::{VelosiAstNode, VelosiAstType};
use crate::error::{VelosiAstErr, VelosiAstErrDoubleDef};
use crate::VelosiTokenStream;

///////////////////////////////////////////////////////////////////////////////////////////////////
// Symbol Definition
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a symbol in the AST
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Symbol {
    /// the name of the symbol, its identifier
    pub name: Rc<String>,
    /// the type of the symbol, `int|bool|...`
    pub typeinfo: VelosiAstType,
    /// the astnode of this symbol
    pub ast_node: VelosiAstNode,
}

/// Implementation of [Symbol]
impl Symbol {
    /// creates a new symbol from the given context and name, type
    pub fn new(name: Rc<String>, typeinfo: VelosiAstType, ast_node: VelosiAstNode) -> Self {
        Symbol {
            name,
            typeinfo,
            ast_node,
        }
    }

    /// obtains the location of the symbol
    pub fn loc(&self) -> &VelosiTokenStream {
        self.ast_node.loc()
    }
}

/// Implementation of the [Display] trait for [Symbol]
///
/// We display it as a table form kind|type|name
impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self.ast_node {
            VelosiAstNode::Unit(_) => write!(f, "unit|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::Const(_) => write!(f, "const|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::Method(_) => write!(f, "method|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::Param(_) => write!(f, "param|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::State(_) => write!(f, "state|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::StateField(_) => {
                write!(f, "statefield|{:?}|{}", self.typeinfo, self.name)
            }
            VelosiAstNode::StateFieldSlice(_) => {
                write!(f, "statefieldslice|{:?}|{}", self.typeinfo, self.name)
            }
            VelosiAstNode::Interface(_) => {
                write!(f, "interface|{:?}|{}", self.typeinfo, self.name)
            }
            VelosiAstNode::InterfaceField(_) => {
                write!(f, "interfacefield|{:?}|{}", self.typeinfo, self.name)
            }
            VelosiAstNode::InterfaceFieldSlice(_) => {
                write!(f, "interfacefieldslice|{:?}|{}", self.typeinfo, self.name)
            }
            VelosiAstNode::Flags(_) => write!(f, "flags|{:?}|{}", self.typeinfo, self.name),
            VelosiAstNode::Flag(_) => {
                write!(f, "flag|{:?}|{}", self.typeinfo, self.name)
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
// Symbol Tabel Context
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a symbol table context
///
/// The symbol table context is contains the symbols that are introduced by the current
/// scope, e.g., unit or method contxt.
#[derive(PartialEq, Eq, Clone, Debug)]
struct SymbolTableContext {
    /// the symbols of the table, we use a vector
    syms: HashMap<String, Symbol>,
    /// the currenct context
    ctxt: String,
}

impl SymbolTableContext {
    /// tries to insert a new symbol into the context
    fn insert(&mut self, sym: Symbol) -> Result<(), VelosiAstErr> {
        match self.syms.get(sym.name.as_str()) {
            None => {
                self.syms.insert(sym.name.to_string(), sym);
                Ok(())
            }
            Some(x) => Err(VelosiAstErrDoubleDef::new(
                sym.name.clone(),
                x.ast_node.loc().clone(),
                sym.ast_node.loc().clone(),
            )
            .into()),
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

///////////////////////////////////////////////////////////////////////////////////////////////////
// Symbol Tabel
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Represents a symbol table
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct SymbolTable {
    /// A vector of symbol table contexts
    syms: Vec<SymbolTableContext>,
}

/// Implementation of [SymbolTable]
impl SymbolTable {
    /// creates a new empty symbol table
    pub fn new() -> Self {
        let mut st = SymbolTable { syms: Vec::new() };
        st.create_context(String::from("global"));
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
        if self.syms.len() > 1 {
            self.syms.pop();
        }
    }

    /// tries to insert the symbol into the current context
    pub fn insert(&mut self, sym: Symbol) -> Result<(), VelosiAstErr> {
        match self.lookup(&sym.name) {
            None => {
                let ctxt = self.syms.last_mut().unwrap();
                ctxt.insert(sym)
            }
            Some(x) => Err(VelosiAstErrDoubleDef::new(
                sym.name.clone(),
                x.ast_node.loc().clone(),
                sym.ast_node.loc().clone(),
            )
            .into()),
        }
    }

    /// checks if there is a corresponding entry in the table
    pub fn contains(&self, sym: &str) -> bool {
        self.syms.iter().any(|x| x.contains(sym))
    }

    /// tries to lookup a symbol by the name in all contexts
    pub fn lookup(&self, name: &str) -> Option<&Symbol> {
        for ctxt in &self.syms {
            let sym = ctxt.lookup(name);
            if sym.is_some() {
                return sym;
            }
        }
        None
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

/// the default implementation
impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}
