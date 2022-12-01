// Velosiraptor Code Generator
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

//! Segment Code Generation (C)

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crustal as C;

use velosiast::ast::{
    VelosiAstExpr, VelosiAstMethod, VelosiAstUnitSegment, VelosiOpExpr, VelosiOperation,
};

use super::utils;
use crate::VelosiCodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in &unit.consts {
        utils::add_const_def(scope, c);
    }
}

fn add_unit_flags(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let structname = format!("{}_flags", unit.ident());
    if let Some(flags) = &unit.flags {
        scope.new_comment("Defined unit flags");

        let st = scope.new_struct(&structname);

        for flag in &flags.flags {
            let f = st.new_field(flag.ident(), C::Type::new_uint64());
            f.set_bitfield_width(1);
        }
    } else {
        scope.new_comment("Unit has no defined flags");
        scope.new_struct(&structname);
    }
    let tyname = format!("{}_t", structname);
    scope.new_typedef(&tyname, C::Type::new_struct(&structname));
}

// /// adds the struct definition of the unit to the scope
// fn add_struct_definition(scope: &mut C::Scope, unit: &Unit) {
//     // a field is a struct
//     //
//     // field_name  --> struct FieldName {  val: u64 };

//     // create the struct in the scope
//     let st = scope.new_struct(unit.ident());

//     // make it public
//     st.vis("pub");

//     // add the doc field to the struct
//     st.doc(&format!(
//         "Represents the Unit type '{}'.\n@loc: {}",
//         unit.ident(),
//         unit.location()
//     ));

//     // it has a single field, called 'val'
//     //st.field("val", to_rust_type(field.nbits()));
// }

fn add_constructor_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let fname = utils::constructor_fn_name(unit.ident());

    let unittype = C::Type::new_typedef(&utils::segment_type_name(unit));

    let mut fun = C::Function::with_string(fname, unittype);
    fun.set_static().set_inline();

    let mut params = Vec::new();
    for p in &unit.params {
        let param = fun.new_param(p.ident(), C::Type::new_uint64()).to_expr();
        params.push((p.ident(), param));
    }

    let body = fun.body();

    let unittype = C::Type::new_typedef(&utils::segment_type_name(unit));
    let tunit = body.new_variable("targetunit", unittype).to_expr();

    for (name, p) in params {
        let n = utils::unit_struct_field_name(name);
        body.assign(C::Expr::field_access(&tunit, &n), p);
    }

    body.return_expr(tunit);

    scope.push_function(fun);
}

fn state_field_access(unit: &str, path: &[String]) -> C::Expr {
    let unit_var = C::Expr::new_var("unit", C::Type::new_void());
    if path.len() == 1 {
        let fname = utils::if_field_rd_fn_name_str(unit, &path[0]);
        return C::Expr::fn_call(&fname, vec![unit_var]);
    }

    if path.len() == 2 {
        let fname = utils::if_field_rd_slice_fn_name_str(unit, &path[0], &path[1]);
        return C::Expr::fn_call(&fname, vec![unit_var]);
    }

    panic!("unhandled!")
}

fn add_translate_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    // let fname = utils::translate_fn_name(unit.ident());

    // let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    // fun.set_static().set_inline();

    // let mut field_vars = HashMap::new();
    // let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit.ident())));

    // let v = fun.new_param("unit", unittype);
    // field_vars.insert(String::from("unit"), v.to_expr());
    // fun.new_param("va", C::Type::new_uint64());
    // fun.new_param("pa", C::Type::new_uint64().to_ptr());

    // if !unit.state().is_memory() {
    //     fun.body().return_expr(C::Expr::bfalse());
    //     scope.push_function(fun);
    //     return;
    // }

    // if let Some(f) = unit.get_method("translate") {
    //     let body = fun.body();

    //     for c in &f.requires {
    //         body.new_ifelse(&C::Expr::not(expr_to_cpp(unit.ident(), c)))
    //             .then_branch()
    //             .new_return(Some(&C::Expr::bfalse()));
    //     }

    //     if let Some(stmt) = &f.stmts {
    //         body.merge(stmt_to_cpp(unit.ident(), stmt));
    //     }
    // } else {
    //     fun.body().new_comment("there was no translate method");
    // }

    // if !(va < 4096) || state.pte.present != 1 {
    //    return false;
    // }
    // *pa = va + (state.pte.base << 12);
    // return true;

    // fun.new_param("size", C::Type::new_size());
    // fun.new_param("pa", C::Type::new_uint64());
    // fun.new_param("flags", C::Type::new_int(64));

    // scope.push_function(fun);
}

fn add_op_fn(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, op: &VelosiAstMethod) {
    let fname = utils::op_fn_name(unit, op);
    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());

    for f in op.params.iter() {
        fun.new_param(f.ident(), utils::ptype_to_ctype(&f.ptype, unit));
    }

    if !op.ops.is_empty() {
        let mut fields = HashSet::new();
        for op in &op.ops {
            let fname = op.fieldname();
            if fname.is_empty() {
                continue;
            }
            fields.insert(String::from(fname));
        }
        fun.body().new_comment("field variables");

        for field in &fields {
            if let Some(f) = unit.interface.field(field) {
                // get the field from the unit
                let field_type = utils::field_type_name(unit, f);

                let var = fun
                    .body()
                    .new_variable(field, C::Type::new_typedef(&field_type));

                let fncall_name = utils::field_set_raw_fn_name(unit, f);
                var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
                field_vars.insert(field.clone(), var.to_expr());
            }
        }

        fun.body().new_comment("configuration sequence");
        for op in &op.ops {
            utils::op_to_c_expr(unit.ident(), fun.body(), op, &field_vars);
        }
    } else {
        fun.body().new_comment("there is no configuration sequence");
    }

    scope.push_function(fun);
}

fn add_map_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let m_fn = unit.get_method("map").unwrap();
    add_op_fn(scope, unit, m_fn);
}

fn add_unmap_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let m_fn = unit.get_method("unmap").unwrap();
    add_op_fn(scope, unit, m_fn);
}

fn add_protect_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let m_fn = unit.get_method("protect").unwrap();
    add_op_fn(scope, unit, m_fn);
}

/// generates the VelosiAstUnitSegment definitions
pub fn generate(unit: &VelosiAstUnitSegment, outdir: &Path) -> Result<(), VelosiCodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.ident());
    utils::add_header(s, &title);

    s.new_include("interface.h", false);

    // add the definitions
    add_unit_constants(s, unit);
    add_unit_flags(s, unit);
    add_constructor_function(s, unit);
    add_map_function(s, unit);
    add_unmap_function(s, unit);
    add_protect_function(s, unit);
    add_translate_function(s, unit);

    // save the scope
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;

    Ok(())
}
