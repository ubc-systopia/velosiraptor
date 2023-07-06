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

use std::ops::Deref;
use std::path::Path;
use crustal as C;
use velosiast::{VelosiAstField, VelosiAstInterfaceField, VelosiAst, VelosiAstUnit};
use crate::fastmodels::add_header;
use crate::fastmodels::state::{state_class_name, state_header_file};
use crate::VelosiHwGenError;

pub fn registers_header_file(name: &str) -> String {
    format!("{}_registers.hpp", name)
}

pub fn registers_header_file_path(name: &str) -> String {
    registers_header_file(name)
}

pub fn registers_impl_file(name: &str) -> String {
    format!("{}_registers.cpp", name)
}

pub fn registers_class_name(name: &str) -> String {
    format!("{}{}Register", name[0..1].to_uppercase(), &name[1..])
}

// defines what interface fields we care about. Currently mmio only.
pub fn register_map<T>(
    func: impl Fn(&VelosiAstInterfaceField) -> T,
    unit: &VelosiAstUnit
) -> Vec<T> {
    if unit.interface().is_none() {
        return vec!();
    }
    return unit.interface().unwrap().fields()
        .iter().filter_map(
            |f| match f.deref() {
                VelosiAstInterfaceField::Memory(_) => None,
                VelosiAstInterfaceField::Register(_) => None,
                VelosiAstInterfaceField::Mmio(_) => Some(func(f.deref())),
            }).collect()

}

pub fn generate_register_header(
    pkgname: &str,
    ast: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();
    add_header(&mut scope, pkgname, "interface registers");

    let hdrguard = format!("{}_REGISTERS_HPP_", pkgname.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", false);
    s.new_include("framework/register_base.hpp", false);

    s.new_comment("translation register specific includes");
    let statehdr = state_header_file(pkgname);
    s.new_include(&statehdr, false);

    for u in ast.units() {
        let rcns = register_map(|r| r.ident().clone(), u);
        for rcn in rcns {
            let c = s.new_class(rcn.as_str());
            c.set_base("RegisterBase", C::Visibility::Public);

            let scn = state_class_name(pkgname);
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

    }

    // done, save the scope
    let filename = registers_header_file_path(pkgname);
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_register_impl(
    name: &str,
    ast: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiHwGenError> {

    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "interface registers");

    // adding the includes
    scope.new_comment("framework includes");
    scope.new_include("framework/types.hpp", false);
    scope.new_include("framework/logging.hpp", false);
    scope.new_comment("translation register specific includes");
    let reghdr = registers_header_file(name);
    scope.new_include(&reghdr, false);

    for u in ast.units() {
        let rs = register_map(|r| r.clone(), u);

        for r in &rs {
            let rcn = r.ident();
            let c = scope.new_class(rcn.as_str());
            c.set_base("RegisterBase", C::Visibility::Public);

            let scn = state_class_name(name);
            let sctype = C::Type::new_class(&scn);
            let state_ptr_type = C::Type::to_ptr(&sctype);

            let stvar = C::Expr::new_var("st", state_ptr_type.clone());

            let cons = c.new_constructor();

            let cparam = C::MethodParam::new("state", state_ptr_type);

            let r_offset = match r {
                VelosiAstInterfaceField::Memory(m) => m.offset,
                VelosiAstInterfaceField::Register(_) => 0,
                VelosiAstInterfaceField::Mmio(m) => m.offset,
            };

            cons.push_parent_initializer(C::Expr::fn_call(
                "RegisterBase",
                vec![
                    C::Expr::new_str(r.ident()),
                    C::Expr::ConstNum(r_offset),
                    C::Expr::ConstNum(r.size()),
                    C::Expr::Raw(String::from("ACCESS_PERMISSION_ALL")),
                    C::Expr::ConstNum(0),
                    C::Expr::from_method_param(&cparam),
                ],
            )).push_param(cparam);

            let mut field_access_expr =
                C::Expr::method_call(&stvar, &format!("{}_field", r.ident()), vec![]);
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
    }

    // set the outfile name
    let filename = registers_impl_file(name);
    scope.set_filename(&filename);

    scope.to_file(outdir, false)?;

    Ok(())
}
