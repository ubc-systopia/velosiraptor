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

// the defined errors
use velosiast::ast::VelosiAstState;
use crate::fastmodels::add_header;
use crate::fastmodels::fields::{state_fields_class_name, state_fields_header_file};
use crate::VelosiHwGenError;

/// generates the name of the state header file
pub fn state_header_file(name: &str) -> String {
    format!("{}_state.hpp", name)
}

/// generates the path of the state header file
pub fn state_header_file_path(name: &str) -> String {
    format!("{}", state_header_file(name))
}

/// generates the name of the state header file
pub fn state_impl_file(name: &str) -> String {
    format!("{}_state.cpp", name)
}

/// generates the state class name
pub fn state_class_name(name: &str) -> String {
    format!("{}{}State", name[0..1].to_uppercase(), &name[1..])
}

pub fn generate_state_header(name: &str, state: &VelosiAstState, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    let scn = state_class_name(name);

    add_header(&mut scope, name, "state");

    // set the header guard
    let guard = scope.new_ifdef(format!("{}_STATE_HPP_", name.to_uppercase()).as_str());

    // create the scope guard
    let s = guard.guard().then_scope();

    s.new_comment("system includes");
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", true);
    s.new_include("framework/state_base.hpp", true);

    s.new_comment("translation unit specific includes");
    let fieldshdr = state_fields_header_file(name);
    s.new_include(&fieldshdr, true);

    // create a new class in the scope
    let c = s.new_class(scn.as_str());

    c.push_doc_str("Represents the State of the Translation Unit.");
    c.set_base("StateBase", C::Visibility::Public);

    c.new_constructor();

    // adding field getters and setters
    for f in state.fields() {
        let fcn = state_fields_class_name(&f.ident());
        let ty = C::Type::new_class(&fcn);

        let fieldname = format!("_{}", f.ident());

        // the field access expression: this->_field
        let e_field_acc = C::Expr::field_access(&C::Expr::this(), &fieldname);

        // get/set the field
        let methodname = format!("{}_field", f.ident());
        let m = c.new_method(&methodname, C::Type::to_ptr(&ty));

        m.set_public()
            .set_inside_def()
            .body()
            .return_expr(C::Expr::addr_of(&e_field_acc));

        // get/set the field values
        let methodname = format!("get_{}_val", f.ident());
        let m = c.new_method(&methodname, C::Type::new(C::BaseType::new_int(f.size())));
        m.set_public()
            .set_inside_def()
            .body()
            .return_expr(C::Expr::method_call(&e_field_acc, "get_value", vec![]));

        let methodname = format!("set_{}_val", f.ident());
        let arg = C::MethodParam::new("val", C::Type::new(C::BaseType::new_int(f.size())));
        let argexpr = C::Expr::from_method_param(&arg);
        let m = c.new_method(&methodname, C::Type::new_void());
        m.set_public()
            .set_inside_def()
            .push_param(arg)
            .body()
            .method_call(e_field_acc, "set_value", vec![argexpr]);
    }

    // adding the state fields to the class
    for f in state.fields() {
        let ty = C::BaseType::Class(state_fields_class_name(&f.ident()));
        let fieldname = format!("_{}", f.ident());
        c.new_attribute(&fieldname, C::Type::new(ty));
    }

    // save the scope
    let filename = state_header_file_path(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_state_impl(name: &str, state: &VelosiAstState, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    let scn = state_class_name(name);

    add_header(&mut scope, name, "state");

    // #include "pv/RemapRequest.h"

    scope.new_comment("fastmodels includes");
    scope.new_include("pv/RemapRequest.h", true);

    scope.new_comment("framework includes");
    scope.new_include("framework/logging.hpp", true);
    scope.new_include("framework/state_field_base.hpp", true);

    scope.new_comment("unit includes");
    let statehdr = state_header_file(name);
    scope.new_include(&statehdr, true);

    let c = scope.new_class(scn.as_str());
    let cons = c.new_constructor();

    cons.push_parent_initializer(C::Expr::fn_call("StateBase", vec![]));

    for f in state.fields() {
        let fieldname = format!("_{}", f.ident());
        let fieldclass = state_fields_class_name(&f.ident());
        cons.push_initializer(fieldname.as_str(), C::Expr::fn_call(&fieldclass, vec![]));

        let this = C::Expr::this();
        let field = C::Expr::field_access(&this, &fieldname);
        cons.body()
            .method_call(C::Expr::this(), "add_field", vec![C::Expr::addr_of(&field)]);
    }

    let filename = state_impl_file(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, false)?;

    Ok(())
}
