// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada
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

//! # The FastModels Platform Generator: State
//!
//! This module generates the state description of the Arm FastModels implementation
//! of the translation unit.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;
use custom_error::custom_error;

// the defined errors
use crate::ast::State;
use crate::hwgen::HWGenError;

pub fn to_state_class_name(name: &str) -> String {
    format!("{}{}State", name[0..1].to_uppercase(), &name[1..])
}

pub fn generate_state_header(name: &str, state: &State, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();
    scope.set_filename("include/state.hpp");

    let scn = to_state_class_name(name);

    scope.push_doc_str(format!("The State of the '{}' Translation Unit\n\n", scn).as_str());
    scope.push_doc_str("WARNING: This file is auto-generated by the  Velosiraptor compiler.\n");

    // set the header guard
    let guard = scope.new_ifdef(format!("{}_STATE_HPP_", name.to_uppercase()).as_str());

    // create the scope guard
    let s = guard.guard().then_scope();

    s.new_comment("system includes");
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("generic/types.hpp", true);
    s.new_include("generic/state_base.hpp", true);

    // create a new class in the scope
    let c = s.new_class(scn.as_str());

    c.push_doc_str("Represents the State of the Translation Unit.");
    c.set_base("StateBase", C::Visibility::Public);

    c.new_constructor();

    // adding field getters and setters
    for f in state.fields() {
        let ty = C::Type::new(C::BaseType::Class(String::from("StateFieldBase"), vec![]));

        let fieldname = format!("_{}", f.name);

        // the field access expression: this->_field
        let e_field_acc = C::Expr::field_access(&C::Expr::this(), &fieldname);

        // get/set the field
        let methodname = format!("get_{}_field", f.name);
        let m = c.new_method(&methodname, C::Type::from_ptr(&ty));

        m.public()
            .inside_def()
            .push_stmt(C::Stmt::retval(e_field_acc.clone()));

        // get/set the field values
        let methodname = format!("get_{}_val", f.name);
        let m = c.new_method(&methodname, C::Type::new(C::BaseType::new_int(f.nbits())));
        m.public()
            .inside_def()
            .push_stmt(C::Stmt::retval(C::Expr::method_call(
                &e_field_acc,
                "get_value",
                vec![],
            )));

        let methodname = format!("set_{}_val", f.name);
        let arg = C::MethodParam::new("val", C::Type::new(C::BaseType::new_int(f.nbits())));
        let argexpr = C::Expr::from_method_param(&arg);
        let m = c.new_method(&methodname, C::Type::new(C::BaseType::new_int(f.nbits())));
        m.public()
            .inside_def()
            .push_argument(arg)
            .push_stmt(C::Stmt::FnCall(C::Expr::method_call(
                &e_field_acc,
                "set_value",
                vec![argexpr],
            )));
    }

    // adding the state fields to the class
    for f in state.fields() {
        let ty = C::BaseType::Class(String::from("StateFieldBase"), vec![]);
        let fieldname = format!("_{}", f.name);
        c.new_attribute(&fieldname, C::Type::new(ty));
    }

    // save the scope
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_state_impl(name: &str, state: &State, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    let scn = to_state_class_name(name);

    scope.set_filename("state.cpp");

    scope.push_doc_str(format!("The State of the '{}' Translation Unit\n\n", scn).as_str());
    scope.push_doc_str("WARNING: This file is auto-generated by the  Velosiraptor compiler.\n");

    // #include "pv/RemapRequest.h"

    scope.new_comment("fastmodels includes");
    scope.new_include("pv/RemapRequest.h", true);

    scope.new_comment("framework includes");
    scope.new_include("generic/logging.hpp", true);
    scope.new_include("generic/state_field_base.hpp", true);

    scope.new_comment("unit includes");
    scope.new_include("state.hpp", true);

    let c = scope.new_class(scn.as_str());
    let cons = c.new_constructor();

    cons.push_parent_initializer(C::Expr::fn_call("StateBase", vec![]));

    for f in state.fields() {
        let fieldname = format!("_{}", f.name);
        cons.push_initializer(
            fieldname.as_str(),
            C::Expr::fn_call(
                "StateFieldBase",
                vec![
                    C::Expr::ConstString(f.name.clone()),
                    C::Expr::ConstNum(f.length),
                    C::Expr::ConstNum(0),
                ],
            ),
        );

        let this = C::Expr::this();
        let field = C::Expr::field_access(&this, &fieldname);
        cons.push_stmt(C::Stmt::fn_call(C::Expr::method_call(
            &this,
            "add_field",
            vec![C::Expr::addr_of(&field)],
        )));
    }

    scope.to_file(outdir, false)?;

    Ok(())
}
