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
    pub imports: Vec<Import>,
    /// the declared constants
    pub consts: Vec<Const>,
    /// the defined units of in the AST
    pub units: Vec<Unit>,
}

use crate::parser::Parser;

impl Ast {
    /// resolves imports recursively
    ///
    /// Walks the import tree and tries to parse each import individually
    /// The function returns an error on the first parser error or when
    /// a cyclic dependency was detected
    fn do_parse_imports(&mut self, path: &mut Vec<String>) -> Result<(), VrsError<TokenStream>> {
        // adding ourselves to the imports
        //        imports.insert(self.filename.clone(), true);

        // get the import file, the parent directory of the current one
        let mut importfile = match Path::new(&self.filename).parent() {
            Some(d) => PathBuf::from(d),
            None => PathBuf::from("./"),
        };

        // add ourselves to the path
        path.push(self.filename.clone());

        // walk through the imports at this level and warn about double imports
        let mut currentimports: HashMap<String, Import> = HashMap::new();
        for i in self.imports.drain(..) {
            match currentimports.get(&i.name) {
                Some(imp) => {
                    let msg = format!("{} is already imported ", i.name);
                    let hint = format!("remove this import");
                    VrsError::new_warn(imp.pos.clone(), msg, Some(hint)).print();
                }
                None => {
                    currentimports.insert(i.name.clone(), i);
                }
            }
        }

        // loop over the current imports
        for (_, mut val) in currentimports.drain() {
            // add the file to the current path
            importfile.push(&val.to_filename().as_str());

            // the file name to be imported
            let filename = importfile.as_path().display().to_string();

            // check if we know about this import already
            if !path.contains(&filename) {
                let mut ast = match Parser::parse_file(filename.as_str()) {
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

                // parsing succeeded, recurse abort if there is an error downstream
                match ast.do_parse_imports(path) {
                    Err(err) => {
                        let msg = String::from("while processing imports from");
                        return Err(VrsError::stack(val.pos.clone(), msg, err));
                    }
                    _ => (),
                }
                // update the ast value
                val.ast = Some(ast);
                // add it back to the import list of the current ast
                self.imports.push(val);
            } else {
                // we have a circular dependency
                let it = path.iter().skip_while(|e| *e != &filename);
                // now convert to string
                let s = it
                    .map(|s| s.to_string())
                    .collect::<Vec<String>>()
                    .join(" -> ");
                if !s.is_empty() {
                    let msg = format!("circular dependency detected:\n  {} -> {}", s, filename);
                    let hint = String::from("try removing the following import");
                    return Err(VrsError::new_err(val.pos.clone(), msg, Some(hint)));
                }
            }
            // restore file path again
            importfile.pop();
        }

        // remove us from the path and return
        path.pop();
        Ok(())
    }

    /// recursively resolves all the imports
    pub fn parse_imports(&mut self) -> Result<(), AstError> {
        // create the hashmap of the imports
        //let mut imports = HashMap::new();
        let mut path = Vec::new();
        match self.do_parse_imports(&mut path) {
            Ok(()) => Ok(()),
            Err(error) => Err(AstError::ImportError { error }),
        }
    }

    fn do_collect_asts(&mut self, asts: &mut HashMap<String, Ast>) {
        self.imports = self
            .imports
            .drain(..)
            .map(|mut i| match i.ast {
                Some(mut ast) => {
                    ast.do_collect_asts(asts);
                    asts.insert(ast.filename.clone(), ast);
                    i.ast = None;
                    i
                }
                None => i,
            })
            .collect();
    }

    /// flattens and merges the import tree
    pub fn merge_imports(&mut self) -> Result<(), AstError> {
        // step one: collect the list of files
        let mut asts = HashMap::new();
        self.do_collect_asts(&mut asts);

        // now we have all the asts read, we can start merging them
        // let mut units = HashMap::new();
        // for u in self.units.drain(..) {
        //     match units.get(&u.name) {
        //         Some(unit) => {
        //             let msg = format!("duplicate unit definition with name {}", u.name);
        //             let hint = format!("the previous position was here");
        //             VrsError::new_err(unit.pos.clone(), msg, Some(hint)).print();
        //         }
        //         None => {
        //             units.insert(u.name.clone(), u);
        //         }
        //     }
        // }

        //     error[E0201]: duplicate definitions with name `do_collect_asts`:
        //     --> src/ast/ast.rs:176:5
        //      |
        //  164 | /     fn do_collect_asts(&mut self, asts : &mut HashMap<String, Ast>) {
        //  165 | |         self.imports = self.imports.drain(..).map(|mut i| match i.ast {
        //  166 | |                 Some(mut ast) => {
        //  167 | |                     ast.do_collect_asts(asts);
        //  ...   |
        //  174 | |         ).collect();
        //  175 | |     }
        //      | |_____- previous definition of `do_collect_asts` here
        //  176 | /     fn do_collect_asts(&mut self) {
        //  177 | |
        //  178 | |     }
        //      | |_____^ duplicate definition

        let mut consts: HashMap<String, Const> = HashMap::new();
        for c in self.consts.drain(..) {
            match consts.get(c.ident()) {
                Some(co) => {
                    let msg = format!("duplicate const definition with name {}", c.ident());
                    let hint = format!("duplicate definition");
                    VrsError::new_err(co.pos().clone(), msg, Some(hint)).print();
                }
                None => {
                    consts.insert(String::from(c.ident()), c);
                }
            }
        }

        for (_, mut ast) in asts.drain() {
            for c in ast.consts.drain(..) {
                match consts.get(c.ident()) {
                    Some(co) => {
                        VrsError::new_double(
                            c.ident().to_string(),
                            c.pos().clone(),
                            co.pos().clone(),
                        )
                        .print();
                    }
                    None => {
                        consts.insert(String::from(c.ident()), c);
                    }
                }
            }
        }
        //     for u in ast.units.drain(..) {

        //     }
        // }

        Ok(())
    }

    /// parses and merges the imports
    pub fn resolve_imports(&mut self) -> Result<(), AstError> {
        self.parse_imports()?;
        self.merge_imports()
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

use crate::ast::AstNode;
impl AstNode for Ast {
    fn check(&self) -> (u32, u32) {
        let mut res = (0, 0);
        // try to insert other constants into this ast
        for c in self.consts.iter() {
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
        assert!(ast.resolve_imports().is_ok());

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

        // lex the file
        let mut ast = match Parser::parse_file(&filename) {
            Ok((ast, _)) => ast,
            Err(x) => panic!("parsing failed:\n\n{}\n\n", x),
        };

        // now resolve the import
        assert!(ast.resolve_imports().is_ok());

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

        // lex the file
        let mut ast = match Parser::parse_file(&filename) {
            Ok((ast, _)) => ast,
            Err(x) => panic!("parsing failed:\n\n{}\n\n", x),
        };

        // now resolve the import
        assert!(ast.resolve_imports().is_err());

        d.pop();
    }
}
