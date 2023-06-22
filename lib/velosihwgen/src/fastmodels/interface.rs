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

//! # The FastModels Platform Generator: Interface
//!
//! This module generates the state description of the Arm FastModels implementation
//! of the translation unit.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;

use velosiast::VelosiAstField;
// the defined errors
use velosiast::ast::VelosiAstInterface;
use crate::fastmodels::add_header;
use crate::fastmodels::registers::{registers_class_name, registers_header_file};
use crate::fastmodels::state::{state_class_name, state_header_file};
use crate::VelosiHwGenError;

/// generates the name of the state field header file
pub fn interface_header_file(name: &str) -> String {
    format!("{}_interface.hpp", name)
}

/// generates the path of the headefile
pub fn interface_header_file_path(name: &str) -> String {
    format!("{}", interface_header_file(name))
}

/// generates the name of the state field header file
pub fn interface_impl_file(name: &str) -> String {
    format!("{}_interface.cpp", name)
}

/// generates the name of the interface class
pub fn interface_class_name(name: &str) -> String {
    format!("{}{}Interface", name[0..1].to_uppercase(), &name[1..])
}

pub fn generate_interface_header(
    name: &str,
    state: &VelosiAstInterface,
    outdir: &Path,
) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "interface");

    // set the header guard
    let hdrguard = format!("{}_INTERFACE_HPP_", name.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // adding includes
    s.new_comment("system includes");
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", false);
    s.new_include("framework/interface_base.hpp", false);

    s.new_comment("translation unit specific includes");
    let statehdr = state_header_file(name);
    s.new_include(&statehdr, false);

    // TODO: make this dependent on the interface type
    let reghdr = registers_header_file(name);
    s.new_include(&reghdr, false);

    // create a new class in the scope
    let icn = interface_class_name(name);
    let c = s.new_class(icn.as_str());
    c.set_base("InterfaceBase", C::Visibility::Public);

    let scn = state_class_name(name);
    let state_ptr_type = C::Type::to_ptr(&C::Type::new_class(&scn));

    let cons = c.new_constructor();
    cons.new_param("state", state_ptr_type.clone());

    // add the state attribute
    c.new_attribute("_state", state_ptr_type);

    for f in state.fields() {
        let rcn = registers_class_name(&f.ident());
        let fieldname = format!("_{}", &f.ident());
        let ty = C::Type::new_class(&rcn);
        c.new_attribute(&fieldname, ty);
    }

    // save the scope
    let filename = interface_header_file_path(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_interface_impl(
    name: &str,
    state: &VelosiAstInterface,
    outdir: &Path,
) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    // adding the header
    add_header(&mut scope, name, "interface");

    // adding the includes
    scope.new_comment("fastmodels includes");
    scope.new_include("pv/RemapRequest.h", true);

    scope.new_comment("framework includes");
    scope.new_include("framework/logging.hpp", false);

    scope.new_comment("unit includes");
    let reghdr = registers_header_file(name);
    scope.new_include(&reghdr, false);
    let ifhdr = interface_header_file(name);
    scope.new_include(&ifhdr, false);

    let icn = interface_class_name(name);
    let c = scope.new_class(icn.as_str());

    let scn = state_class_name(name);
    let state_ptr_type = C::Type::to_ptr(&C::Type::new_class(&scn));

    let cons = c.new_constructor();

    let m = cons.new_param("state", state_ptr_type);

    let pa = C::Expr::from_method_param(m);

    cons.push_parent_initializer(C::Expr::fn_call("InterfaceBase", vec![pa.clone()]));
    cons.push_initializer("_state", pa.clone());

    for f in state.fields() {
        let fieldname = format!("_{}", f.ident());
        let rcn = registers_class_name(&f.ident());
        cons.push_initializer(fieldname.as_str(), C::Expr::fn_call(&rcn, vec![pa.clone()]));

        let this = C::Expr::this();
        let field = C::Expr::field_access(&this, &fieldname);
        cons.body().method_call(
            C::Expr::this(),
            "add_register",
            vec![C::Expr::addr_of(&field)],
        );
    }

    let filename = interface_impl_file(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, false)?;

    Ok(())
}
