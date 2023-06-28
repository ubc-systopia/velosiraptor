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

use velosiparser::{VelosiParseTreeIdentifier, VelosiParseTreeMethod, VelosiTokenStream};

use crate::ast::{
    VelosiAstBinOp, VelosiAstExpr, VelosiAstIdentLiteralExpr, VelosiAstIdentifier, VelosiAstNode,
    VelosiAstParam, VelosiAstType, VelosiAstTypeInfo, VelosiOperation,
};
use crate::error::{VelosiAstErrBuilder, VelosiAstIssues};
use crate::{ast_result_return, ast_result_unwrap, utils, AstResult, Symbol, SymbolTable};

/// the signature of the translate function
pub const FN_SIG_VALID: &str = "fn valid() -> bool";
pub const FN_SIG_TRANSLATE: &str = "fn translate(va: vaddr) -> addr";
pub const FN_SIG_MATCHFLAGS: &str = "fn matchflags(flgs:flags) -> bool";
pub const FN_SIG_MAP: &str = "fn map(va: vaddr, sz: size, flgs: flags, pa: paddr)";
pub const FN_SIG_UNMAP: &str = "fn unmap(va: vaddr, sz: size)";
pub const FN_SIG_PROTECT: &str = "fn protect(va: vaddr, sz: size, flgs: flags)";

// const FN_SIG_INIT: &str = "fn init()";

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum VelosiAstMethodProperty {
    Invariant,
    Predicate,
}

impl VelosiAstMethodProperty {
    pub fn from_parse_tree(
        pt: VelosiParseTreeIdentifier,
        _st: &mut SymbolTable,
    ) -> AstResult<Self, VelosiAstIssues> {
        match pt.name.as_str() {
            "invariant" => AstResult::Ok(Self::Invariant),
            "predicate" => AstResult::Ok(Self::Predicate),
            _ => {
                let msg = "unknown method property";
                let hint = "supported method properties are `invariant` and `predicate`";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pt.loc)
                    .build();
                AstResult::Err(VelosiAstIssues::from(err))
            }
        }
    }
}

impl Display for VelosiAstMethodProperty {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Invariant => write!(f, "invariant"),
            Self::Predicate => write!(f, "predicate"),
        }
    }
}

#[derive(Eq, Clone, Debug)]
pub struct VelosiAstMethod {
    /// the name of the constant
    pub ident: VelosiAstIdentifier,
    /// properties of the method
    pub properties: HashSet<VelosiAstMethodProperty>,
    /// whether this is an abstract method
    pub is_abstract: bool,
    /// wheather this is a method to be synthesized
    pub is_synth: bool,
    /// the return type
    pub rtype: VelosiAstType,
    /// the method parameter
    pub params: Vec<Rc<VelosiAstParam>>,
    /// a map from parameter name to the parameter
    pub params_map: HashMap<String, Rc<VelosiAstParam>>,
    /// preconditions
    pub requires: Vec<Rc<VelosiAstExpr>>,
    /// method body
    pub body: Option<Rc<VelosiAstExpr>>,
    /// synthesized operations
    pub ops: Vec<VelosiOperation>,
    /// the location of the import clause
    pub loc: VelosiTokenStream,
}

impl VelosiAstMethod {
    pub fn new(
        ident: VelosiAstIdentifier,
        rtype: VelosiAstType,
        params: Vec<Rc<VelosiAstParam>>,
        requires: Vec<Rc<VelosiAstExpr>>,
        body: Option<Rc<VelosiAstExpr>>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        params.iter().for_each(|p| {
            params_map.insert(p.ident_to_string(), p.clone());
        });
        Self {
            ident,
            properties: HashSet::new(),
            is_abstract: false,
            is_synth: false,
            rtype,
            params,
            params_map,
            requires,
            body,
            ops: Vec::new(),
            loc,
        }
    }

    pub fn new_abstract(
        ident: VelosiAstIdentifier,
        rtype: VelosiAstType,
        params: Vec<Rc<VelosiAstParam>>,
        requires: Vec<Rc<VelosiAstExpr>>,
        body: Option<Rc<VelosiAstExpr>>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        params.iter().for_each(|p| {
            params_map.insert(p.ident_to_string(), p.clone());
        });
        Self {
            ident,
            properties: HashSet::new(),
            is_abstract: true,
            is_synth: false,
            rtype,
            params,
            params_map,
            requires,
            body,
            ops: Vec::new(),
            loc,
        }
    }

    pub fn new_synth(
        ident: VelosiAstIdentifier,
        rtype: VelosiAstType,
        params: Vec<Rc<VelosiAstParam>>,
        requires: Vec<Rc<VelosiAstExpr>>,
        body: Option<Rc<VelosiAstExpr>>,
        loc: VelosiTokenStream,
    ) -> Self {
        let mut params_map = HashMap::new();
        params.iter().for_each(|p| {
            params_map.insert(p.ident_to_string(), p.clone());
        });
        Self {
            ident,
            properties: HashSet::new(),
            is_abstract: false,
            is_synth: true,
            rtype,
            params,
            params_map,
            requires,
            body,
            ops: Vec::new(),
            loc,
        }
    }

    pub fn default_map() -> Self {
        Self::new_synth(
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
        Self::new_synth(
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
        Self::new_synth(
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
            Some(Rc::new(VelosiAstExpr::IdentLiteral(
                VelosiAstIdentLiteralExpr::with_name("va".to_string(), VelosiAstTypeInfo::VirtAddr),
            ))), // just true
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
            Vec::new(),                                             // no requires
            Some(Rc::new(VelosiAstExpr::BoolLiteral(true.into()))), // just true
            VelosiTokenStream::default(),                           // no location
        )
    }

    pub fn default_valid() -> Self {
        Self::new(
            VelosiAstIdentifier::with_name("valid".to_string()),
            VelosiAstType::new_bool(),
            Vec::new(),
            Vec::new(),                                             // no requires
            Some(Rc::new(VelosiAstExpr::BoolLiteral(true.into()))), // just true
            VelosiTokenStream::default(),                           // no location
        )
    }

    /// obtains a reference to the identifier
    pub fn ident(&self) -> &Rc<String> {
        self.ident.ident()
    }

    /// obtains a copy of the identifer
    pub fn ident_to_string(&self) -> String {
        self.ident.as_str().to_string()
    }

    /// obtains a reference to the fully qualified path
    pub fn path(&self) -> &Rc<String> {
        &self.ident.path
    }

    /// obtains a copy of the fully qualified path
    pub fn path_to_string(&self) -> String {
        self.ident.path.as_str().to_string()
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

        // convert the properties
        let mut properties: HashSet<VelosiAstMethodProperty> = HashSet::new();
        for p in pt.properties.into_iter() {
            let loc = p.loc.clone();
            let prop = ast_result_unwrap!(VelosiAstMethodProperty::from_parse_tree(p, st), issues);

            if properties.contains(&prop) {
                let msg = "ignoring double defined property";
                let hint = "remove the duplicate property";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(loc)
                    .build();

                issues.push(err);
            } else {
                properties.insert(prop);
            }
        }

        // convert all the unit parameters
        let mut params = Vec::new();
        for p in pt.params.into_iter() {
            let param = Rc::new(ast_result_unwrap!(
                VelosiAstParam::from_parse_tree(p, true, st),
                issues
            ));

            // for the flags we need to add the flags to the symbol table
            if param.ptype.is_flags() {
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
                    flags.populate_symboltable(param.ident(), st);
                }
            }

            // add the param to the symbol table, if it doesn't exist already
            if let Err(e) = st.insert(param.clone().into()) {
                issues.push(*e);
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

            if !exp.result_type().is_boolean() {
                // check that the expression is boolean
                let msg = "Requires clause has incompatible type ";
                let hint = format!("Expected boolean, found {}", exp.result_type());
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

        // a simple filter with obvioius duplicates
        let mut requires_set = HashSet::new();
        let requires = requires
            .into_iter()
            .filter(|r| {
                let r_str = r.to_string();
                if !requires_set.contains(&r_str) {
                    requires_set.insert(r_str);
                    true
                } else {
                    false
                }
            })
            .collect();

        let body = if let Some(b) = pt.body {
            let body = ast_result_unwrap!(VelosiAstExpr::from_parse_tree(b, st), issues);

            // check the return type matches the body
            if !rtype.typeinfo.compatible(body.result_type()) {
                let msg = "Method body has incomptaible type. ";
                let hint = if rtype.is_boolean() {
                    format!("Expected boolean, found {}", body.result_type())
                } else if rtype.is_void() {
                    format!("Expected (), found {}", body.result_type())
                } else {
                    format!(
                        "Expected [`bool`, `int`, `size`, `addr`], found {}",
                        body.result_type()
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

            Some(Rc::new(body.into_cnf(st)))
        } else {
            None
        };

        // the method was abstract or synth but has a body...
        if body.is_some() && (pt.is_abstract || pt.is_synth) {
            let (ms, range) = match (pt.is_abstract, pt.is_synth) {
                (true, true) => ("abstract & synth ", 0..2),
                (false, true) => ("synth ", 0..1),
                (true, false) => ("abstract ", 0..1),
                (false, false) => unreachable!(),
            };
            let msg = format!("method defined as {ms} cannot have a body.");
            let hint = format!("remove the `{ms}` modifier");
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint)
                .add_location(pt.pos.from_self_with_subrange(range))
                .build();
            issues.push(err);
        }

        // the method has no body but is not abstract
        if body.is_none() && !(pt.is_abstract || pt.is_synth) {
            let msg = "method with no body must be declared abstract or synth.";
            let hint = "make this an `abstract fn` or `synth fn`";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.pos.from_self_with_subrange(0..1))
                .build();
            issues.push(err);
        }

        // doesn't make sense to have abstract synth, let's just do a warning instad
        if pt.is_abstract && pt.is_synth {
            let msg = "declaring a synth method abstract has no effect.";
            let hint = "remove the `abstract` modifier";
            let err = VelosiAstErrBuilder::warn(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(pt.pos.from_self_with_subrange(0..1))
                .build();
            issues.push(err);
        }

        // check a few things regarding the properties
        if !properties.is_empty() {
            if !rtype.is_boolean() {
                let msg = "methods with properties must have a boolean return type.";
                let hint = "change this to `fn -> bool`";
                let err = VelosiAstErrBuilder::warn(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(rtype.loc.clone())
                    .build();
                issues.push(err);
            }
        }

        // restore the symbol table context
        st.drop_context();

        let mut res = if pt.is_abstract {
            Self::new_abstract(name, rtype, params, requires, body, pt.pos)
        } else if pt.is_synth {
            Self::new_synth(name, rtype, params, requires, body, pt.pos)
        } else {
            Self::new(name, rtype, params, requires, body, pt.pos)
        };

        if !properties.is_empty() {
            res.properties = properties;
        }

        // perform additional checks for one of the special methods
        res.check_special_methods(&mut issues);

        ast_result_return!(res, issues)
    }

    /// obtains the parameter with the given name
    pub fn get_param(&self, name: &str) -> Option<&Rc<VelosiAstParam>> {
        self.params_map.get(name)
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
            let msg = format!("mismatched return type in special method: `{sig}`");
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
                .add_location(self.loc.from_self_with_subrange(0..2))
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
            let msg = format!("mismatched number of parameter in special method: `{sig}`");
            let hint = format!("expected {}, found {}", params.len(), self.params.len());
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint)
                .add_location(self.loc.clone())
                .build();
            issues.push(err);
        }

        for (i, p) in self.params.iter().enumerate() {
            if i >= params.len() {
                let msg = format!("unexpected parameter in special method: `{sig}`");
                let hint = "remove this parameter of the function";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
                continue;
            }
            if p.ident().as_str() != params[i].0 {
                let msg = format!("mismatch of parameter name in special method: `{sig}`");
                let hint = format!("expected {}, found {}", params[i].0, p.ident());
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint)
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
            }

            if p.ptype.typeinfo != params[i].1 {
                let msg = format!("mismatch of parameter type in special method: `{sig}`");
                let hint = format!("expected {}, found {}", params[i].1, p.ptype);
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint)
                    .add_location(p.loc.clone())
                    .build();
                issues.push(err);
            }
        }
    }

    fn check_not_synth(&self, issues: &mut VelosiAstIssues) {
        if self.is_synth {
            let msg = "this special method should not be synth";
            let hint = "remove the `synth`";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(self.loc.from_self_with_subrange(0..1))
                .build();
            issues.push(err);
        }
    }

    fn check_translate_preconds(&self, issues: &mut VelosiAstIssues) {
        let mut params = HashSet::new();
        for p in self.params.iter() {
            params.insert(p.ident().as_str());
        }

        for pre in self.requires.iter() {
            if !pre.has_state_references() {
                continue;
            }

            if !pre.has_var_references(&params) {
                continue;
            }

            let mut format_mismatch = true;
            if let VelosiAstExpr::BinOp(pre) = pre.as_ref() {
                let mut found = false;
                if let VelosiAstExpr::IdentLiteral(i) = pre.lhs.as_ref() {
                    found |= params.contains(i.ident().as_str());
                }

                if let VelosiAstExpr::IdentLiteral(i) = pre.rhs.as_ref() {
                    found |= params.contains(i.ident().as_str());
                }

                format_mismatch = !(found
                    & matches!(
                        pre.op,
                        // VelosiAstBinOp::Eq
                        //     | VelosiAstBinOp::Ne
                        |VelosiAstBinOp::Lt| VelosiAstBinOp::Gt
                            | VelosiAstBinOp::Le
                            | VelosiAstBinOp::Ge
                    ));
            }

            if format_mismatch {
                let msg = "unsupported mixed pre-condition form detected.";
                let hint = "remove this precondition or convert it to ident [<,>, <=, >=] expr";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(pre.loc().clone())
                    .build();
                issues.push(err);
            }
        }
    }

    fn check_special_methods(&self, issues: &mut VelosiAstIssues) {
        match self.ident().as_str() {
            "valid" => {
                self.check_rettype(issues, FN_SIG_VALID, VelosiAstTypeInfo::Bool);
                self.check_arguments_exact(issues, FN_SIG_VALID, &[]);
                self.check_not_synth(issues);
            }
            "translate" => {
                self.check_rettype(issues, FN_SIG_TRANSLATE, VelosiAstTypeInfo::PhysAddr);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_TRANSLATE,
                    &[("va", VelosiAstTypeInfo::VirtAddr)],
                );
                self.check_not_synth(issues);
                self.check_translate_preconds(issues);
            }
            "matchflags" => {
                // fn matchflags(flgs: flags) -> bool
                self.check_rettype(issues, FN_SIG_MATCHFLAGS, VelosiAstTypeInfo::Bool);
                self.check_arguments_exact(
                    issues,
                    FN_SIG_MATCHFLAGS,
                    &[("flgs", VelosiAstTypeInfo::Flags)],
                );
                self.check_not_synth(issues);
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
            .map(|p| p.ident().clone())
            .collect()
    }

    pub fn get_param_names(&self) -> HashSet<&str> {
        let mut params = HashSet::new();
        for p in self.params.iter() {
            params.insert(p.ident().as_str());
        }
        params
    }
}

/// Implementation fo the [From] trait for [Symbol]
impl From<Rc<VelosiAstMethod>> for Symbol {
    fn from(c: Rc<VelosiAstMethod>) -> Self {
        let n = VelosiAstNode::Method(c.clone());
        Symbol::new(c.path().clone(), c.rtype.clone(), n)
    }
}

/// Implementation of [PartialEq] for [VelosiAstStaticMapElement]
impl PartialEq for VelosiAstMethod {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
        && self.is_abstract == other.is_abstract
        && self.is_synth == other.is_synth
        && self.rtype == other.rtype
        && self.params == other.params
        // params map is the same as params
        && self.requires == other.requires
        && self.body == other.body
        && self.ops == other.ops
    }
}

/// Implementation of [Display] for [VelosiAstMethod]
impl Display for VelosiAstMethod {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if !self.properties.is_empty() {
            write!(f, "  #[")?;
            for (i, prop) in self.properties.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{prop}")?;
            }
            writeln!(f, "]")?;
        }

        write!(f, "  ")?;
        if self.is_abstract {
            write!(f, "abstract ")?;
        }
        if self.is_synth {
            write!(f, "synth ")?;
        }
        write!(f, "fn {}(", self.ident())?;
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
                writeln!(f, "    requires {r};")?;
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
