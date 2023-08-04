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

use crate::fastmodels::add_header;
use crate::VelosiHwGenError;
use crustal as C;
use std::path::Path;
use velosiast::VelosiAstUnit;

pub fn state_header_file(name: &str) -> String {
    format!("{}_state.hpp", name)
}

pub fn state_header_file_path(name: &str) -> String {
    state_header_file(name)
}

pub fn state_impl_file(name: &str) -> String {
    format!("{}_state.cpp", name)
}

pub fn state_class_name(name: &str) -> String {
    format!("{}{}State", name[0..1].to_uppercase(), &name[1..])
}

pub fn state_field_class_name(name: &str) -> String {
    format!("{}{}StateField", name[0..1].to_uppercase(), &name[1..])
}

// TODO: I don't know how helpful it is to separate the header from the implementation
// It may just make this file more confusing.

pub fn generate_state_header(unit: &VelosiAstUnit, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    let scn = state_class_name(unit.ident());

    add_header(&mut scope, unit.ident(), "state");

    let guard =
        scope.new_ifdef(format!("{}_STATE_HPP_", unit.ident().to_uppercase()).as_str());

    let s = guard.guard().then_scope();

    s.new_comment("system includes");
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_include("framework/types.hpp", false);
    s.new_include("framework/state_base.hpp", false);
    s.new_include("framework/state_field_base.hpp", false);

    match unit.state() {
        None => {
            s.new_comment("This unit has an empty state");
            s.new_comment(&format!("Abstract:  {}", unit.is_abstract()));
            s.new_comment(&format!("Enum:      {}", unit.is_enum()));
            s.new_comment(&format!("Staticmap: {}", unit.is_staticmap()));
            s.new_class(&scn) //empty state
                .set_base("StateBase", C::Visibility::Public);
        }

        Some(state) => {
            // one class for each field
            for f in state.fields() {
                let rcn = state_field_class_name(f.ident());
                let f_c = s
                    .new_class(&rcn)
                    .set_base("StateFieldBase", C::Visibility::Public);
                f_c.new_constructor();

                let var = C::Expr::new_var("data", C::Type::new_uint(64));

                // TODO: The per-slice getters and setters may or may not be helpful.
                // Keeping them for now, but I don't plan to call them
                for sl in &f.layout_as_slice().to_vec() {
                    let sl_getter_f = format!("get_{}_val", sl.ident());
                    let m = f_c
                        .new_method(&sl_getter_f, C::Type::new_uint(64))
                        .set_public()
                        .set_inline();

                    m.body().return_expr(C::Expr::method_call(
                        &C::Expr::this(),
                        "get_slice_value",
                        vec![C::Expr::new_str(sl.ident())],
                    ));
                    let sl_setter_f = format!("set_{}_val", sl.ident());
                    let m = f_c
                        .new_method(&sl_setter_f, C::Type::new_void())
                        .set_public()
                        .set_inline();
                    m.new_param("data", C::Type::new_int(64));
                    m.body().method_call(
                        C::Expr::this(),
                        "set_slice_value",
                        vec![C::Expr::new_str(sl.ident()), var.clone()],
                    );
                }
            }

            // one class for state containing all fields
            let c = s.new_class(&scn);
            c.set_base("StateBase", C::Visibility::Public);
            c.new_constructor();

            for f in state.fields() {
                let ty = C::BaseType::Class(state_field_class_name(f.ident()));
                c.new_attribute(f.ident(), C::Type::new(ty))
                    .set_visibility(C::Visibility::Public);
            }
        }
    }

    let filename = state_header_file_path(unit.ident());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_state_impl(unit: &VelosiAstUnit, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    let scn = state_class_name(unit.ident());

    add_header(&mut scope, unit.ident(), "state");

    scope.new_comment("fastmodels includes");
    scope.new_include("pv/RemapRequest.h", true);

    scope.new_comment("framework includes");
    scope.new_include("framework/logging.hpp", false);

    scope.new_comment("unit includes");
    let statehdr = state_header_file(unit.ident());
    scope.new_include(&statehdr, false);

    match unit.state() {
        None => (),
        Some(state) => {
            for f in state.fields() {
                let rcn = state_field_class_name(f.ident());
                let f_c = scope.new_class(rcn.as_str());
                f_c.set_base("StateFieldBase", C::Visibility::Public);

                let cons = f_c.new_constructor();
                cons.push_parent_initializer(C::Expr::fn_call(
                    "StateFieldBase",
                    vec![
                        C::Expr::new_str(f.ident()),
                        C::Expr::new_num(f.size()),
                        C::Expr::new_num(0),
                    ],
                ));

                for sl in &f.layout_as_slice().to_vec() {
                    cons.body().method_call(
                        C::Expr::this(),
                        "add_slice",
                        vec![
                            C::Expr::new_str(sl.ident()),
                            C::Expr::new_num(sl.start),
                            C::Expr::new_num(sl.end),
                        ],
                    );
                }
            }

            let c = scope.new_class(scn.as_str());
            let cons = c.new_constructor();

            cons.push_parent_initializer(C::Expr::fn_call("StateBase", vec![]));

            for f in state.fields() {
                let fieldname = f.ident();
                let fieldclass = state_field_class_name(f.ident());
                cons.push_initializer(fieldname.as_str(), C::Expr::fn_call(&fieldclass, vec![]));

                let this = C::Expr::this();
                let field = C::Expr::field_access(&this, fieldname);
                cons.body().method_call(
                    C::Expr::this(),
                    "add_field",
                    vec![C::Expr::addr_of(&field)],
                );
            }
        }
    }

    let filename = state_impl_file(unit.ident());
    scope.set_filename(&filename);
    scope.to_file(outdir, false)?;

    Ok(())
}
