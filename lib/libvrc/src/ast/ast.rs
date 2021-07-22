// Velosiraptor ParseTree
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

//! Ast representation of the VelosiRaptor Definitions

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

use crate::ast::{AstError, Const, Import, Unit};
use crate::error::VrsError;
use crate::parser::ParserError;
use crate::token::TokenStream;

/// represents the ast of a parsed file.
///
/// The parsed file consists of three possible directives:
///   1. imports: references to other files
///   2. constants: pre-defined values
///   3. units: units defined in this file
#[derive(PartialEq, Clone)]
pub struct Ast {
    /// the filename this ast represents
    pub filename: String,
    /// the import statements found in the Ast
    pub imports: HashMap<String, Import>,
    /// the declared constants
    pub consts: HashMap<String, Const>,
    /// the defined units of in the AST
    pub units: HashMap<String, Unit>,
}

use crate::parser::Parser;

impl Ast {
    pub fn merge(&mut self, other: Ast) {
        //
        let mut other = other;
        // try to insert other constants into this ast
        for (key, val) in other.imports.drain() {
            // check if the key is already there, that's an error
            if !self.imports.contains_key(&key) {
                self.imports.insert(key, val);
            }
        }

        // try to insert other constants into this ast
        for (key, val) in other.consts.drain() {
            // check if the key is already there, that's an error
            if self.consts.contains_key(&key) {
                let c = self.consts.get(&key).unwrap();
                let pos = c.pos();

                panic!(
                    "error in {} - double defined constant. '{}' already defined here {}",
                    pos,
                    key,
                    val.pos()
                );
            }

            self.consts.insert(key, val);
        }

        // try to insert the other units into this ast
        for (key, val) in other.units.drain() {
            // check if the key is already there, that's an error
            if self.units.contains_key(&key) {
                let c = self.consts.get(&key).unwrap();
                let pos = c.pos();

                panic!(
                    "error in {} - double defined unit. '{}' already defined here {}",
                    pos,
                    key,
                    val.pos()
                );
            }

            self.units.insert(key, val);
        }
    }

    /// resolves imports recursively
    fn do_resolve_imports(
        &mut self,
        imports: &mut HashMap<String, bool>,
        path: &mut Vec<String>,
    ) -> Result<(), VrsError<TokenStream>> {
        // adding ourselves to the imports
        imports.insert(self.filename.clone(), true);

        let mut importfile = match Path::new(&self.filename).parent() {
            Some(d) => PathBuf::from(d),
            None => PathBuf::from("./"),
        };

        // add ourselves
        path.push(self.filename.clone());

        // loop over the current imports
        for (key, val) in self.imports.iter_mut() {
            let filename = val.to_filename();
            importfile.push(&filename);

            let f = importfile.as_path().to_str().unwrap();

            // check if we know about this import already
            if !imports.contains_key(f) {
                let mut ast = match Parser::parse_file(f) {
                    Ok((ast, _)) => ast,
                    Err(ParserError::LexerFailure { error }) => {
                        let msg = String::from("during lexing of the file");
                        return Err(VrsError::stack(val.pos.clone(), msg, error));
                    }
                    Err(ParserError::ParserFailure { error }) => {
                        let msg = String::from("during parsing of the file");
                        return Err(VrsError::stack(val.pos.clone(), msg, error));
                    }
                    Err(ParserError::ParserIncomplete { error }) => {
                        let msg = String::from("unexpected junk at the end of the file");
                        return Err(VrsError::stack(val.pos.clone(), msg, error));
                    }

                    Err(x) => panic!("foobar {:?}", x),
                };
                // resolve the imports
                match ast.do_resolve_imports(imports, path) {
                    Err(err) => {
                        let msg = String::from("while processing imports from");
                        return Err(VrsError::stack(val.pos.clone(), msg, err));
                    }
                    _ => (),
                }

                // update the ast
                val.ast = Some(ast);
            } else {
                // check if we have a circular dependency...
                let it = path.iter();
                // skip over the elements that are not the key
                let it = it.skip_while(|e| *e != f);
                // now convert to string
                let s = it
                    .map(|s| s.to_string())
                    .collect::<Vec<String>>()
                    .join(" -> ");
                if !s.is_empty() {
                    let msg = format!("circular dependency detected:\n  {} -> {}", s, f);
                    let hint = String::from("try removing the following import");
                    return Err(VrsError::new_err(val.pos.clone(), msg, Some(hint)));
                }
            }
            importfile.pop();
        }
        // remove from path
        path.pop();
        Ok(())
    }

    /// recursively resolves all the imports
    pub fn resolve_imports(&mut self) -> Result<(), AstError> {
        // create the hashmap of the imports
        let mut imports = HashMap::new();
        let mut path = Vec::new();
        match self.do_resolve_imports(&mut imports, &mut path) {
            Ok(()) => Ok(()),
            Err(error) => Err(AstError::ImportError { error }),
        }
    }

    /// merges the imports together
    fn merge_imports(&mut self) {
        let mut imports = Vec::new();
        let mut newimports = HashMap::new();
        for (key, mut import) in self.imports.drain() {
            import.ast = match import.ast {
                Some(mut ast) => {
                    ast.merge_imports();
                    imports.push(ast);
                    None
                }
                None => None,
            };
            newimports.insert(key, import);
        }
        // update the new imports
        self.imports = newimports;

        for import in imports.drain(..) {
            self.merge(import);
        }
    }

    ///
    pub fn check_consistency(&self) {
        self.check();
    }
}

/// implementation of the [fmt::Display] trait for the [Ast].
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Ast: TODO",)
    }
}

/// implementation of the [fmt::Debug] display trait for the [Ast].
impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Ast: TODO",)
    }
}

use crate::ast::AstCheck;
impl AstCheck for Ast {
    fn check(&self) -> (u32, u32) {
        let mut res = (0, 0);
        // try to insert other constants into this ast
        for (_, c) in self.consts.iter() {
            let val = c.check();
            res = (res.0 + val.0, res.1 + val.1)
        }
        res
    }
}

#[test]
fn import_test_ok() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/imports");

    for f in vec!["basicimport.vrs", "multiimport.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        println!("filename: {}", filename);

        // lex the file
        let mut ast = match Parser::parse_file(&filename) {
            Ok((ast, _)) => ast,
            Err(x) => panic!("parsing failed:\n\n{}\n\n", x),
        };

        // now resolve the import
        ast.resolve_imports();

        d.pop();
    }
}

#[test]
fn import_test_recursive() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/imports");

    for f in vec!["recursiveimport.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());

        println!("filename: {}", filename);

        // lex the file
        let mut ast = match Parser::parse_file(&filename) {
            Ok((ast, _)) => ast,
            Err(x) => panic!("parsing failed:\n\n{}\n\n", x),
        };

        // now resolve the import
        ast.resolve_imports();

        d.pop();
    }
}

#[test]
fn import_test_circular() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/imports");

    for f in vec!["circular21.vrs", "circular1.vrs"] {
        d.push(f);
        let filename = format!("{}", d.display());
        println!("====================================");
        println!("filename: {}", filename);

        // lex the file
        let mut ast = match Parser::parse_file(&filename) {
            Ok((ast, _)) => ast,
            Err(x) => panic!("parsing failed:\n\n{}\n\n", x),
        };

        // now resolve the import
        ast.resolve_imports();

        d.pop();
    }
}
