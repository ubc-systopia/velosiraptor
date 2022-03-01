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
//! This module generates the field description of the Arm FastModels implementation
//! of the translation state.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;

// the defined errors
use crate::ast::State;
use crate::hwgen::fastmodels::add_header;
use crate::hwgen::HWGenError;

/// generates the name of the state field header file
pub fn state_fields_header_file(name: &str) -> String {
    format!("{}_state_fields.hpp", name)
}

/// generates the path of the header file
pub fn state_fileds_header_file_path(name: &str) -> String {
    format!("include/{}", state_fields_header_file(name))
}

/// generates the name of the state field header file
pub fn state_fields_impl_file(name: &str) -> String {
    format!("{}_state_fields.cpp", name)
}

/// generates the state fields class name
pub fn state_fields_class_name(name: &str) -> String {
    format!("{}{}StateField", name[0..1].to_uppercase(), &name[1..])
}

/// generates the method name for obtaining the slices of a field value
pub fn state_fields_slice_getter_name(name: &str) -> String {
    format!("get_{}_val", name)
}

/// generates the method name for setting the slices of a field value
pub fn state_fields_slice_setter_name(name: &str) -> String {
    format!("set_{}_val", name)
}

/// generates the header file for the  state fields
pub fn generate_field_header(name: &str, state: &State, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "state fields");

    // set the header guard
    let hdrguard = format!("{}_FIELDS_HPP_", name.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // adding the includes
    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", true);
    s.new_include("framework/state_field_base.hpp", true);

    // generate a new class for each field
    for f in state.fields() {
        // create a new class in the scope
        let rcn = state_fields_class_name(&f.name);
        let c = s.new_class(&rcn);

        // set the base class
        c.set_base("StateFieldBase", C::Visibility::Public);

        // add a new constructor
        c.new_constructor();

        // the variable
        let var = C::Expr::new_var("data", C::Type::new_uint(64));

        for sl in &f.layout {
            let slname = state_fields_slice_getter_name(&sl.name);
            let m = c
                .new_method(&slname, C::Type::new_uint(64))
                .set_public()
                .set_inline();
            m.body()
                .variable(C::Variable::new("data", C::Type::new_uint(64)))
                .method_call(
                    C::Expr::this(),
                    "get_slice_value",
                    vec![C::Expr::new_str(&sl.name), C::Expr::addr_of(&var)],
                )
                .return_expr(var.clone());

            let slname = state_fields_slice_setter_name(&sl.name);
            let m = c
                .new_method(&slname, C::Type::new_void())
                .set_public()
                .set_inline();
            m.new_param("data", C::Type::new_int(64));
            m.body().method_call(
                C::Expr::this(),
                "set_slice_value",
                vec![C::Expr::new_str(&sl.name), var.clone()],
            );
        }
    }

    // set the filename for this scope
    let filename = state_fileds_header_file_path(name);
    scope.set_filename(&filename);

    // save the scope
    scope.to_file(outdir, true)?;

    Ok(())
}

/// generates the implementation file for the state fields
pub fn generate_field_impl(name: &str, state: &State, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "state fields");

    // adding includes
    scope.new_comment("framework includes");
    scope.new_include("framework/types.hpp", true);
    scope.new_comment("translation unit generic includes");
    let hdrfile = state_fields_header_file(name);
    scope.new_include(&hdrfile, true);

    for f in state.fields() {
        let rcn = state_fields_class_name(&f.name);
        // create a new class in the scope
        let c = scope.new_class(rcn.as_str());
        c.set_base("StateFieldBase", C::Visibility::Public);

        let cons = c.new_constructor();
        cons.push_parent_initializer(C::Expr::fn_call(
            "StateFieldBase",
            vec![
                C::Expr::new_str(&f.name),
                C::Expr::new_num(f.nbits()),
                C::Expr::new_num(0),
            ],
        ));

        for sl in &f.layout {
            cons.body().method_call(
                C::Expr::this(),
                "add_slice",
                vec![
                    C::Expr::new_str(&sl.name),
                    C::Expr::new_num(sl.start),
                    C::Expr::new_num(sl.end),
                ],
            );
        }
    }

    // set the filename for this scope
    let filename = state_fields_impl_file(name);
    scope.set_filename(&filename);

    // save the scope
    scope.to_file(outdir, false)?;

    Ok(())
}
