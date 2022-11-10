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

//! # VelosiAst -- Method Definitions
//!
//! This module defines the Method AST nodes of the langauge

use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::rc::Rc;

use velosiparser::{VelosiParseTreeMethod, VelosiTokenStream};

use crate::ast::{
    VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstIdentifier, VelosiAstNode, VelosiAstParam,
    VelosiAstType, VelosiAstTypeInfo,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

/// the signature of the translate function
pub const FN_SIG_TRANSLATE: &str = "fn translate(va: vaddr) -> addr";
pub const FN_SIG_MATCHFLAGS: &str = "fn matchflags(flgs:flags) -> bool";
pub const FN_SIG_MAP: &str = "fn map(va: vaddr, sz: size, flgs: flags, pa: addr)";
pub const FN_SIG_UNMAP: &str = "fn unmap(va: vaddr, sz: size)";
pub const FN_SIG_PROTECT: &str = "fn protect(va: vaddr, sz: size, flgs: flags)";
// const FN_SIG_INIT: &str = "fn init()";

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct VelosiAstMethod {
    /// the name of the constant
    pub ident: VelosiAstIdentifier,
    /// the return type
    pub rtype: VelosiAstType,
    /// the method parameter
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map from parameter name to the parameter
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// preconditions
    pub requires: Vec<VelosiAstExpr>,
    /// method body
    pub body: Option<VelosiAstExpr>,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstMethod {
    pub fn new(
        ident: VelosiAstIdentifier,
        rtype: VelosiAstType,
        params: Vec<Rc<VelosiAstParam>>,
        requires: Vec<VelosiAstExpr>,
        body: Option<VelosiAstExpr>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        params.iter().for_each(|p| {
            params_map.insert(p.ident_to_string(), p.clone());
        });
        Self {
            ident,
            rtype,
            params,
            params_map,
            requires,
            body,
            loc,
        }
    }

    pub fn default_map() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("map".to_string()),
            VelosiAstType::new_void(),
            vec![
                Rc::new(VelosiAstParam::with_name(
                    "va".to_string(),
                    VelosiAstTypeInfo::VirtAddr,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "sz".to_string(),
                    VelosiAstTypeInfo::Size,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "flgs".to_string(),
                    VelosiAstTypeInfo::Flags,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "pa".to_string(),
                    VelosiAstTypeInfo::PhysAddr,
                )),
            ],
            Vec::new(),                   // no requires
            None,                         // no body
            VelosiTokenStream::default(), // no location
        )
    }

    pub fn default_unmap() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("unmap".to_string()),
            VelosiAstType::new_void(),
            vec![
                Rc::new(VelosiAstParam::with_name(
                    "va".to_string(),
                    VelosiAstTypeInfo::VirtAddr,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "sz".to_string(),
                    VelosiAstTypeInfo::Size,
                )),
            ],
            Vec::new(),                   // no requires
            None,                         // no body
            VelosiTokenStream::default(), // no location
        )
    }

    pub fn default_protect() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("protect".to_string()),
            VelosiAstType::new_void(),
            vec![
                Rc::new(VelosiAstParam::with_name(
                    "va".to_string(),
                    VelosiAstTypeInfo::VirtAddr,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "sz".to_string(),
                    VelosiAstTypeInfo::Size,
                )),
                Rc::new(VelosiAstParam::with_name(
                    "flgs".to_string(),
                    VelosiAstTypeInfo::Flags,
                )),
            ],
            Vec::new(),                   // no requires
            None,                         // no body
            VelosiTokenStream::default(), // no location
        )
    }

    pub fn default_translate() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("protect".to_string()),
            VelosiAstType::new_paddr(),
            vec![Rc::new(VelosiAstParam::with_name(
                "va".to_string(),
                VelosiAstTypeInfo::VirtAddr,
            ))],
            Vec::new(), // no requires
            Some(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("va".to_string(), VelosiAstTypeInfo::VirtAddr),
            )), // just true
            VelosiTokenStream::default(), // no location
        )
    }

    pub fn default_matchflags() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("protect".to_string()),
            VelosiAstType::new_bool(),
            vec![Rc::new(VelosiAstParam::with_name(
                "flgs".to_string(),
                VelosiAstTypeInfo::Flags,
            ))],
            Vec::new(),                                    // no requires
            Some(VelosiAstExpr::BoolLiteral(true.into())), // just true
            VelosiTokenStream::default(),                  // no location
        )
    }

    pub fn ident_as_rc_string(&self) -> Rc<String> {
        self.ident.name.clone()
    }

    pub fn ident_as_str(&self) -> &str {
        self.ident.name.as_str()
    }

    pub fn ident_to_string(&self) -> String {
        self.ident.name.to_string()
    }

    // converts the parse tree node into an ast node, performing checks
    pub fn from_parse_tree(
        pt: VelosiParseTreeMethod,
        st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        let mut issues = VelosiAstIssues::new();

        // create a new context in the symbol table
        st.create_context("method".to_string());

        // check whether the name is in the right format
        let name = VelosiAstIdentifier::from(pt.name);
        utils::check_snake_case(&mut issues, &name);

        // convert all the unit parameters
        let mut params = Vec::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, true, st),
                issues
            ));

            // for the flags we need to add the flags to the symbol table
            if param.ptype.is_flags() {
                println!("param is flags!");
                let flags = if let Some(f) = st.lookup("flags") {
                    if let VelosiAstNode::Flags(flags) = &f.ast_node {
                        // clone the RC
                        Some(flags.clone())
                    } else {
                        let msg = "Flags defined as a symbol of different type.";
                        let err = VelosiAstErrBuilder::err(msg.to_string())
                            .add_location(param.loc.clone())
                            .build();
                        issues.push(err);
                        None
                    }
                } else {
                    let msg = "Undefined type `flags` in method parameter.";
                    let hint = "Define the unit flags before using them in the method.";
                    let err = VelosiAstErrBuilder::err(msg.to_string())
                        .add_hint(hint.to_string())
                        .add_location(param.loc.clone())
                        .build();
                    issues.push(err);
                    None
                };

                if let Some(flags) = flags {
                    // add the flags to the symbol table
                    flags.populate_symboltable(param.ident_as_str(), st);
                }
            }

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(e);
            } else {
                params.push(param);
            }
        }

        // obtain the type information, must be a built-in type
        let rtype = if let Some(rtype) = pt.rettype {
            let rtype = ast_result_unwrap!(VelosiAstType::from_parse_tree(rtype, st), issues);
            if !rtype.is_builtin() || rtype.is_flags() {
                let msg = "Unsupported type. Function returns only support of the built-in types.";
                let hint = "Change this type to one of [`bool`, `int`, `size`, `addr`].";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(rtype.loc.clone())
                    .build();
                issues.push(err);
            }
            rtype
        } else {
            // if no return type is specified, we assume it is void
            VelosiAstType::new_void()
        };

        // convert all the unit parameters
        let mut requires = Vec::new();
        for p in pt.requires.into_iter() {
            let exp = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(p, st), issues);

            if !exp.result_type(st).is_boolean() {
                // check that the expression is boolean
                let msg = "Requires clause has incompatible type ";
                let hint = format!("Expected boolean, found {}", exp.result_type(st));
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint)
                    .add_location(exp.loc().clone())
                    .build();
                issues.push(err);
            }

            if exp.has_interface_references() {
                // TODO: could make this a bit better by highlighting the interface reference
                let msg = "Interface references are not allowed in requires clauses.";
                let hint = "Remove interface reference from the predicate";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(exp.loc().clone())
                    .build();
                issues.push(err);
            }

            let exp = exp.into_cnf(st);
            requires.extend(exp.split_cnf());
        }

        let body = if let Some(b) = pt.body {
            let body = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(b, st), issues);

            // check the return type matches the body
            if !rtype.typeinfo.compatible(body.result_type(st)) {
                let msg = "Method body has incomptaible type. ";
                let hint = if rtype.is_boolean() {
                    format!("Expected boolean, found {}", body.result_type(st))
                } else if rtype.is_void() {
                    format!("Expected (), found {}", body.result_type(st))
                } else {
                    format!(
                        "Expected [`bool`, `int`, `size`, `addr`], found {}",
                        body.result_type(st)
                    )
                };
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint)
                    .add_location(body.loc().clone())
                    .build();
                issues.push(err);
            }

            if body.has_interface_references() {
                // TODO: could make this a bit better by highlighting the interface reference
                let msg = "Interface references are not allowed in method bodies";
                let hint = "Remove interface reference from the expression";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(body.loc().clone())
                    .build();
                issues.push(err);
            }

            Some(body)
        } else {
            None
        };

        // restore the symbol table context
        st.drop_context();

        let res = Self::new(name, rtype, params, requires, body, pt.pos);

        // perform additional checks for one of the special methods
        res.check_special_methods(&mut issues);

        ast_result_return!(res, issues)
    }

    /// checks whether the method's return type match the given signature
    ///
    /// # Arguments
    ///
    /// * `self`  - reference of the method
    /// * `sig`   - the signature of the method (just a string)
    /// * `ty`    - the expected return type of the parameter (produces error)
    ///
    /// # Return Value
    ///
    /// The number of issues found with the return type
    ///
    fn check_rettype(&self, issues: &mut VelosiAstIssues, sig: &str, ty: VelosiAstTypeInfo) {
        if self.rtype.typeinfo != ty {
            let msg = format!("mismatched return type in special method: `{}`", sig);
            let hint = format!("expected {}, found {}", ty, self.rtype.typeinfo);
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint)
                .add_location(self.rtype.loc.clone())
                .build();
            issues.push(err);
        }
    }

    fn check_rettype_non_void(&self, issues: &mut VelosiAstIssues) {
        if self.rtype.typeinfo == VelosiAstTypeInfo::Void {
            let msg = "return type `()` is only allowed for map/unmap/protect";
            let hint = format!("expected integer or boolean, found {}", self.rtype.typeinfo);
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(self.rtype.loc.clone())
                .build();
            issues.push(err);
        }
    }

    fn check_arguments_exact(
        &self,
        issues: &mut VelosiAstIssues,
        sig: &str,
        params: &[(&str, VelosiAstTypeInfo)],
    ) {
        if self.params.len() != params.len() {
            let msg = format!(
                "mismatched number of parameter in special method: `{}`",
                sig
            );
            let hint = format!("expected {}, found {}", params.len(), self.params.len());
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint)
                .add_location(self.loc.clone())
                .build();
            issues.push(err);
        }

        for (i, p) in self.params.iter().enumerate() {
            if i >= params.len() {
                let msg = format!("unexpected parameter in special method: `{}`", sig);
                let hint = "remove this parameter of the function";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
                continue;
            }
            if p.ident_as_str() != params[i].0 {
                let msg = format!("mismatch of parameter name in special method: `{}`", sig);
                let hint = format!("expected {}, found {}", params[i].0, p.ident_as_str());
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint)
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
            }

            if p.ptype.typeinfo != params[i].1 {
                let msg = format!("mismatch of parameter type in special method: `{}`", sig);
                let hint = format!("expected {}, found {}", params[i].1, p.ptype);
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint)
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
            }
        }
    }

    fn check_special_methods(&self, issues: &mut VelosiAstIssues) {
        match self.ident_as_str() {
            "translate" => {
                self.check_rettype(issues, FN_SIG_TRANSLATE, VelosiAstTypeInfo::PhysAddr);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_TRANSLATE,
                    &[("va", VelosiAstTypeInfo::VirtAddr)],
                );
            }
            "matchflags" => {
                // fn matchflags(flgs: flags) -> bool
                self.check_rettype(issues, FN_SIG_MATCHFLAGS, VelosiAstTypeInfo::Bool);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_MATCHFLAGS,
                    &[("flgs", VelosiAstTypeInfo::Flags)],
                );
            }
            "map" => {
                // fn map(va: vaddr, sz: size, flgs: flags, pa: paddr)
                self.check_rettype(issues, FN_SIG_MAP, VelosiAstTypeInfo::Void);
                //self.check_arguments_exact(issues, FN_SIG_MAP, &[("va", VelosiAstTypeInfo::VirtAddr), ("sz", VelosiAstTypeInfo::Size), ("flgs", VelosiAstTypeInfo::Flags), ("pa", VelosiAstTypeInfo::PhysAddr)]);
            }
            "unmap" => {
                // fn unmap(va: vaddr, sz: size)
                self.check_rettype(issues, FN_SIG_UNMAP, VelosiAstTypeInfo::Void);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_UNMAP,
                    &[
                        ("va", VelosiAstTypeInfo::VirtAddr),
                        ("sz", VelosiAstTypeInfo::Size),
                    ],
                );
            }
            "protect" => {
                // fn protect(va: vaddr, sz: size, flgs: flags)
                self.check_rettype(issues, FN_SIG_PROTECT, VelosiAstTypeInfo::Void);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_PROTECT,
                    &[
                        ("va", VelosiAstTypeInfo::VirtAddr),
                        ("sz", VelosiAstTypeInfo::Size),
                        ("flgs", VelosiAstTypeInfo::Flags),
                    ],
                );
            }
            _ => {
                self.check_rettype_non_void(issues);
            }
        }
    }

    /// returns a set of state references made by this method's body
    ///
    /// # Arguments
    ///
    /// * `self`  -  reference of the method
    ///
    /// # Return Value
    ///
    /// Hash set of strings containing state references in state.field.slice format
    ///
    pub fn get_state_references_in_body(&self) -> HashSet<Rc<String>> {
        if let Some(body) = &self.body {
            let mut srefs = HashSet::new();
            body.get_state_references(&mut srefs);
            srefs
        } else {
            HashSet::new()
        }
    }

    /// returns a set of state references made by this method's preconditions
    ///
    /// # Arguments
    ///
    /// * `self`  -  reference of the method
    ///
    /// # Return Value
    ///
    /// Hash set of strings containing state references in state.field.slice format
    ///
    pub fn get_state_references_in_preconditions(&self) -> HashSet<Rc<String>> {
        let mut srefs = HashSet::new();
        for p in self.requires.iter() {
            p.get_state_references(&mut srefs);
        }
        srefs
    }

    /// returns a set of state references made by this method
    ///
    /// This includes references made by the statements of the method body,
    /// and the ensures and requires clauses by the methods
    ///
    /// # Arguments
    ///
    /// * `self`  -  reference of the method
    ///
    /// # Return Value
    ///
    /// Hash set of strings containing all state references
    ///
    pub fn get_state_references(&self) -> HashSet<Rc<String>> {
        let mut srefs = self.get_state_references_in_body();
        srefs.extend(self.get_state_references_in_preconditions());
        srefs
    }

    /// obtains the names of method parameters that are of the flags type
    pub fn get_flag_param_names(&self) -> Vec<Rc<String>> {
        self.params
            .iter()
            .filter(|p| p.ptype.is_flags())
            .map(|p| p.ident_as_rc_string())
            .collect()
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstMethod>> for Symbol {
    fn from(c: Rc<VelosiAstMethod>) -> Self {
        let n = VelosiAstNode::Method(c.clone());
        Symbol::new(c.ident_as_rc_string(), c.rtype.clone(), n)
    }
}

/// Implementation of [Display] for [VelosiAstMethod]
impl Display for VelosiAstMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "  fn {}(", self.ident_as_str())?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            Display::fmt(p, f)?;
        }
        write!(f, ") -> {}", self.rtype)?;

        if !self.requires.is_empty() {
            writeln!(f)?;
            for r in &self.requires {
                writeln!(f, "    requires {};", r)?;
            }
        } else {
            writeln!(f, "\n    requires true;")?;
        }

        if let Some(b) = &self.body {
            write!(f, "  {{\n    ")?;
            Display::fmt(b, f)?;
            write!(f, "\n  }}")
        } else {
            write!(f, "  {{ }}")
        }
    }
}
