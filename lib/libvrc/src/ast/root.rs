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

use crate::ast::{
    utils, AstError, AstNodeGeneric, Const, Import, Issues, Segment, StaticMap, SymbolTable, Unit,
};
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
pub struct AstRoot {
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

impl<'a> AstRoot {
    pub fn new(
        filename: String,
        imports: Vec<Import>,
        consts: Vec<Const>,
        units: Vec<Unit>,
    ) -> Self {
        Self {
            filename,
            imports: Vec::new(),
            consts: consts,
            units: units,
        }
    }

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
                    let hint = String::from("remove this import");
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
                        return Err(VrsError::stack(val.pos, msg, error));
                    }
                    Err(ParserError::ParserFailure { error }) => {
                        let msg = String::from("during parsing of the file");
                        return Err(VrsError::stack(val.pos, msg, error));
                    }
                    Err(ParserError::ParserIncomplete { error }) => {
                        let msg = String::from("unexpected junk at the end of the file");
                        return Err(VrsError::stack(val.pos, msg, error));
                    }
                    Err(x) => panic!("foobar {:?}", x),
                };

                // parsing succeeded, recurse abort if there is an error downstream
                if let Err(err) = ast.do_parse_imports(path) {
                    let msg = String::from("while processing imports from");
                    return Err(VrsError::stack(val.pos, msg, err));
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
                    return Err(VrsError::new_err(val.pos, msg, Some(hint)));
                }
            }
            // restore file path again
            importfile.pop();
        }

        // remove us from the path and return
        path.pop();
        Ok(())
    }

    /// recursively resolves all the imports, stops on the first error encountered
    pub fn parse_imports(&mut self) -> Result<(), AstError> {
        // create the hashmap of the imports
        //let mut imports = HashMap::new();
        let mut path = Vec::new();
        match self.do_parse_imports(&mut path) {
            Ok(()) => Ok(()),
            Err(e) => Err(AstError::ImportError { e }),
        }
    }

    /// recursively collects all asts from the imports
    fn do_collect_asts(&mut self, asts: &mut HashMap<String, AstRoot>) {
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

        // count the number of errors we've seen
        let mut errors = 0;

        // now we have all the asts read, we can start merging them

        // start with our own constant and unit definitions
        let mut units = HashMap::new();
        errors += utils::collect_list(&mut self.units, &mut units);

        let mut consts = HashMap::new();
        errors += utils::collect_list(&mut self.consts, &mut consts);

        // now do the same for each AST
        for (_, mut ast) in asts.drain() {
            errors += utils::collect_list(&mut ast.units, &mut units);
            errors += utils::collect_list(&mut ast.consts, &mut consts);
        }

        // now we've collected all units and constants, so we can build the list again
        for (_, u) in units.drain() {
            self.units.push(u);
        }
        for (_, c) in consts.drain() {
            self.consts.push(c);
        }

        // now sort the lists
        self.units.sort_by(|a, b| a.partial_cmp(b).unwrap());
        self.consts.sort_by(|a, b| a.partial_cmp(b).unwrap());

        // return the error count, if we encountered one
        if errors == 0 {
            Ok(())
        } else {
            Err(AstError::MergeError {
                i: Issues::new(errors, 0),
            })
        }
    }

    /// parses and merges the imports
    pub fn resolve_imports(&mut self) -> Result<(), AstError> {
        self.parse_imports()?;
        self.merge_imports()
    }

    pub fn resolve_unit_inheritance(&mut self) -> Result<(), AstError> {
        // build the resolution hashmap.

        let mut derives = HashMap::new();
        for unit in &self.units {
            if unit.name() == "Segment" || unit.name() == "StaticMap" {
                let msg = String::from("Unit names 'Segment' and 'StaticMap' are reserved.");
                let hint = String::from("change the name of the unit to something else.");
                let loc = unit.loc().with_range(1..2);
                VrsError::new_err(loc, msg, Some(hint)).print();
                return Err(AstError::DeriveError {
                    i: Issues::new(1, 0),
                });
            }

            match unit.derived() {
                Some(d) => derives.insert(unit.name().to_string(), Some(d.clone())),
                None => derives.insert(unit.name().to_string(), None),
            };
        }

        for unit in &self.units {
            let mut path = vec![unit.name()];
            let mut derived_from = unit.name();
            loop {
                derived_from = match derives.get(derived_from) {
                    Some(Some(derived)) => derived,
                    Some(None) => {
                        break;
                    }
                    None => {
                        let msg = format!("unknown unit in derives clause of unit {}", unit.name());
                        let loc = unit.loc().with_range(1..5);
                        VrsError::new_err(loc, msg, None).print();
                        return Err(AstError::DeriveError {
                            i: Issues::new(1, 0),
                        });
                    }
                };
                if path.contains(&derived_from) {
                    // we have a circular dependency
                    let it = path.iter().skip_while(|e| *e != &unit.name());
                    // now convert to string
                    let s = it
                        .map(|s| s.to_string())
                        .collect::<Vec<String>>()
                        .join(" -> ");
                    if !s.is_empty() {
                        let msg = format!(
                            "circular dependency on unit derivations detected:  {} -> {}",
                            s,
                            unit.name()
                        );
                        let loc = unit.loc().with_range(1..5);
                        VrsError::new_err(loc, msg, None).print();
                    }
                    // TODO: actually return an error
                    return Err(AstError::DeriveError {
                        i: Issues::new(1, 0),
                    });
                }

                path.push(derived_from);

                if derived_from == "Segment" || derived_from == "StaticMap" {
                    break;
                }
            }

            if derived_from != "Segment" && derived_from != "StaticMap" {
                let msg = format!(
                    "unit '{}' is not derived from 'StaticMap' or 'Segment' ({})",
                    unit.name(),
                    derived_from
                );
                let loc = unit.loc().with_range(1..5);
                VrsError::new_err(loc, msg, None).print();
                return Err(AstError::DeriveError {
                    i: Issues::new(1, 0),
                });
            }
        }

        let mut derives_inv: HashMap<String, Vec<String>> = HashMap::new();
        for (name, derived) in derives.drain() {
            if let Some(derived) = derived {
                match derives_inv.get_mut(&derived) {
                    Some(v) => {
                        v.push(name);
                    }
                    None => {
                        derives_inv.insert(derived, vec![name]);
                    }
                }
            }
        }

        let mut tasks = vec!["Segment", "StaticMap"];

        let mut units = HashMap::new();
        for unit in self.units.drain(..) {
            units.insert(unit.name().to_string(), unit);
        }

        while !tasks.is_empty() {
            let task = tasks.pop().unwrap();
            if let Some(derived) = derives_inv.get(task) {
                for d in derived {
                    let mut u = units.remove(d).unwrap();
                    if task == "Segment" || task == "StaticMap" {
                        // TODO: derive from Segment or StaticMap
                        println!("unit: {} skipping derivation from {}", u.name(), task);
                    } else {
                        let other = self.get_unit(task).unwrap();
                        u.derive(other);
                    }

                    // add the derived unit to the ast and push the task to the queue
                    self.units.push(u);
                    tasks.push(d);
                }
            }
        }

        Ok(())
    }

    pub fn build_symboltable(&self) -> Result<SymbolTable, AstError> {
        let mut err = Issues::ok();
        let mut st = SymbolTable::new();
        for c in &self.consts {
            let sym = c.to_symbol();
            if !st.insert(sym) {
                err.inc_err(1);
            };
        }

        for u in &self.units {
            let sym = u.to_symbol();
            if !st.insert(sym) {
                err.inc_err(1);
            };
        }

        if err.errors > 0 {
            Err(AstError::SymTabError { i: err })
        } else {
            Ok(st)
        }
    }

    /// checks for consistency
    pub fn check_consistency(&'a self, st: &mut SymbolTable<'a>) -> Result<Issues, AstError> {
        let val = self.check(st);
        if val.errors > 0 {
            Err(AstError::CheckError { i: val })
        } else {
            Ok(val)
        }
    }

    // applies AST transformations
    pub fn apply_rewrites(&mut self) {
        for u in &mut self.units {
            u.rewrite();
        }
    }

    ///
    pub fn all_units(&self) -> &[Unit] {
        &self.units
    }

    pub fn segment_units(&self) -> impl Iterator<Item = &Segment> + '_ {
        self.units.iter().filter_map(|u| match u {
            Unit::Segment(s) => Some(s),
            _ => None,
        })
    }

    pub fn segment_units_mut(&mut self) -> impl Iterator<Item = &mut Segment> + '_ {
        self.units.iter_mut().filter_map(|u| match u {
            Unit::Segment(s) => Some(s),
            _ => None,
        })
    }

    pub fn staticmap_units(&self) -> impl Iterator<Item = &StaticMap> + '_ {
        self.units.iter().filter_map(|u| match u {
            Unit::StaticMap(s) => Some(s),
            _ => None,
        })
    }

    pub fn staticmap_units_mut(&mut self) -> impl Iterator<Item = &mut StaticMap> + '_ {
        self.units.iter_mut().filter_map(|u| match u {
            Unit::StaticMap(s) => Some(s),
            _ => None,
        })
    }

    /// obtains the unit with a given name
    pub fn get_unit(&self, name: &str) -> Option<&Unit> {
        self.units.iter().find(|u| u.name() == name)
    }

    pub fn get_unit_mut(&mut self, name: &str) -> Option<&mut Unit> {
        self.units.iter_mut().find(|u| u.name() == name)
    }
}

/// implementation of the [fmt::Display] trait for the [Ast].
impl fmt::Display for AstRoot {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "AST")?;
        writeln!(f, " + Imports:")?;
        for i in &self.imports {
            writeln!(f, "   - {}", i.name())?;
        }
        writeln!(f, " + Constants:")?;
        for c in &self.consts {
            writeln!(f, "   - {}", c)?;
        }
        writeln!(f, " + Units:")?;
        for u in &self.units {
            writeln!(f, "   - {}", u.name())?;
        }
        Ok(())
    }
}

/// implementation of the [fmt::Debug] display trait for the [Ast].
impl fmt::Debug for AstRoot {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Ast: TODO",)
    }
}

/// implementation of [AstNodeGeneric] for [Ast]
impl<'a> AstNodeGeneric<'a> for AstRoot {
    fn check(&'a self, st: &mut SymbolTable<'a>) -> Issues {
        // no issues so far
        let mut res = Issues::ok();

        // sanity check
        for i in self.imports.iter() {
            assert_eq!(i.ast, None);
        }

        // check all constant definitions
        // the constants have already been checked for double defined symbols during the merge
        // phase of the import resolution
        for c in self.consts.iter() {
            let val = c.check(st);
            res = res + val;
        }

        // check the unit definitions
        // the units have already been checked for double definitions during the merge phase of
        // the import resolution
        for u in self.units.iter() {
            let val = u.check(st);
            res = res + val;
        }

        res
    }

    fn name(&self) -> &str {
        "ast"
    }
    /// returns the location of the current
    fn loc(&self) -> &TokenStream {
        unimplemented!()
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
