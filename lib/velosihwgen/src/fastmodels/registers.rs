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
//! This module generates the register description of the Arm FastModels implementation
//! of the translation register.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;

use velosiast::{VelosiAstField, VelosiAstInterfaceField};
// the defined errors
use velosiast::ast::VelosiAstInterface;
use crate::fastmodels::add_header;
use crate::fastmodels::state::{state_class_name, state_header_file};
use crate::HWGenError;

/// generates the name of the state field header file
pub fn registers_header_file(name: &str) -> String {
    format!("{}_registers.hpp", name)
}

/// generates the path of the state field header file
pub fn registers_header_file_path(name: &str) -> String {
    format!("include/{}", registers_header_file(name))
}

/// generates the name of the state field header file
pub fn registers_impl_file(name: &str) -> String {
    format!("{}_registers.cpp", name)
}

/// generates the class name for the registers file
pub fn registers_class_name(name: &str) -> String {
    format!("{}{}Register", name[0..1].to_uppercase(), &name[1..])
}

/// generate the header file for the interface registers
pub fn generate_register_header(
    name: &str,
    interface: &VelosiAstInterface,
    outdir: &Path,
) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // document heaeder
    add_header(&mut scope, name, "interface registers");

    // set the header guard
    let hdrguard = format!("{}_REGISTERS_HPP_", name.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // adding the includes
    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", true);
    s.new_include("framework/register_base.hpp", true);

    s.new_comment("translation register specific includes");
    let statehdr = state_header_file(name);
    s.new_include(&statehdr, true);

    // if the interface is not a register-based interface we skip this
    // if !interface.fields() {
    //     scope.to_file(outdir, true)?;
    //     return Ok(());
    // }

    // for each field in the scope create a register class
    for f in interface.fields() {

        if !matches!(**f, VelosiAstInterfaceField::Register(_)) {
            // scope.to_file(outdir, true)?;
            continue;
        };

        let rcn = registers_class_name(&f.ident());
        // create a new class in the scope
        let c = s.new_class(rcn.as_str());
        c.set_base("RegisterBase", C::Visibility::Public);

        let scn = state_class_name(name);
        let sctype = C::Type::new_class(&scn);
        let state_ptr_type = C::Type::to_ptr(&sctype);

        c.new_constructor().new_param("state", state_ptr_type);

        c.new_method("do_read", C::Type::new_uint(64))
            .set_override()
            .set_public();
        c.new_method("do_write", C::Type::new_void())
            .set_override()
            .set_public()
            .new_param("data", C::Type::new_uint(64));

    }

    // done, save the scope
    let filename = registers_header_file_path(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

/// generate the implementation file for the interface registers
pub fn generate_register_impl(
    name: &str,
    interface: &VelosiAstInterface,
    outdir: &Path,
) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "interface registers");

    // adding the includes
    scope.new_comment("framework includes");
    scope.new_include("framework/types.hpp", true);
    scope.new_include("framework/logging.hpp", true);
    scope.new_comment("translation register specific includes");
    let reghdr = registers_header_file(name);
    scope.new_include(&reghdr, true);

    for f in interface.fields() {
        // if it's not a register file, we skip
        if !matches!(**f, VelosiAstInterfaceField::Register(_)) {
            // scope.to_file(outdir, false)?;
            continue;
        };

        let rcn = registers_class_name(&f.ident());
        // create a new class in the scope
        let c = scope.new_class(rcn.as_str());
        c.set_base("RegisterBase", C::Visibility::Public);

        let scn = state_class_name(name);
        let sctype = C::Type::new_class(&scn);
        let state_ptr_type = C::Type::to_ptr(&sctype);

        let stvar = C::Expr::new_var("st", state_ptr_type.clone());

        let cons = c.new_constructor();

        let cparam = C::MethodParam::new("state", state_ptr_type);
        cons.push_parent_initializer(C::Expr::fn_call(
            "RegisterBase",
            vec![
                C::Expr::new_str(&f.ident()),
                // C::Expr::ConstNum(f.offset()), // TODO probably wrong
                C::Expr::ConstNum(f.size()),
                C::Expr::Raw(String::from("ACCESS_PERMISSION_ALL")),
                C::Expr::ConstNum(0),
                C::Expr::from_method_param(&cparam),
            ],
        ))
        .push_param(cparam);

        let mut field_access_expr =
            C::Expr::method_call(&stvar, &format!("{}_field", f.ident()), vec![]);
        field_access_expr.set_ptr();

        let m = c
            .new_method("do_read", C::Type::new_uint(64))
            .set_override();
        m.body()
            .fn_call(
                "Logging::debug",
                vec![C::Expr::new_str("Register::do_read()")],
            )
            .raw(format!(
                "auto st = static_cast<{} *>(this->get_state())",
                scn
            ))
            .return_expr(C::Expr::method_call(
                &field_access_expr,
                "get_value",
                vec![],
            ));

        let m = c.new_method("do_write", C::Type::new_void()).set_override();
        m.new_param("data", C::Type::new_uint(64));
        m.body()
            .fn_call(
                "Logging::debug",
                vec![C::Expr::new_str("Register::do_write()")],
            )
            .raw(format!(
                "auto st = static_cast<{} *>(this->get_state())",
                scn
            ))
            .method_call(
                field_access_expr,
                "set_value",
                vec![C::Expr::new_var("data", C::Type::new_uint(64))],
            );
    }

    // set the outfile name
    let filename = registers_impl_file(name);
    scope.set_filename(&filename);

    scope.to_file(outdir, false)?;

    Ok(())
}
