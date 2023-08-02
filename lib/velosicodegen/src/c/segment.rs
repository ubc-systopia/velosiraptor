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

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment};
use velosiast::VelosiAstUnit;
use velosicomposition::Relations;

use super::utils::{self, FieldUtils, UnitUtils};
use crate::VelosiCodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in unit.consts() {
        utils::add_const_def(scope, c);
    }
}

fn add_unit_flags(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let structname = unit.to_flags_struct_name();

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

    scope.new_typedef(&unit.to_flags_type(), C::Type::new_struct(&structname));
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
    // define the function
    let mut fun = C::Function::with_string(unit.constructor_fn_name(), unit.to_ctype());
    fun.set_static().set_inline();

    // add the function parameter
    let mut params = Vec::new();
    for p in &unit.params {
        let ty = unit.ptype_to_ctype(&p.ptype.typeinfo);
        let param = fun.new_param(p.ident(), ty).to_expr();
        params.push((p.ident(), param));
    }

    let body = fun.body();

    // declare a new variable
    let tunit = body.new_variable("targetunit", unit.to_ctype()).to_expr();

    // set the fields
    for (name, p) in params {
        body.assign(C::Expr::field_access(&tunit, name), p);
    }

    // add the return expression
    body.return_expr(tunit);

    scope.push_function(fun);
}

// fn state_field_access(unit: &str, path: &[String]) -> C::Expr {
//     let unit_var = C::Expr::new_var("unit", C::Type::new_void());
//     if path.len() == 1 {
//         let fname = utils::if_field_rd_fn_name_str(unit, &path[0]);
//         return C::Expr::fn_call(&fname, vec![unit_var]);
//     }

//     if path.len() == 2 {
//         let fname = utils::if_field_rd_slice_fn_name_str(unit, &path[0], &path[1]);
//         return C::Expr::fn_call(&fname, vec![unit_var]);
//     }

//     panic!("unhandled!")
// }

// fn add_translate_function(_scope: &mut C::Scope, _unit: &VelosiAstUnitSegment) {
// let fname = utils::translate_fn_name(unit.ident());

// let mut fun = C::Function::with_string(fname, C::Type::new_bool());
// fun.set_static().set_inline();

// let mut field_vars = HashMap::new();
// let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.ident())));

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
// }

fn add_valid_fn(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let mut valid = C::Function::with_string(unit.valid_fn_name(), C::Type::new_bool());
    valid.set_static().set_inline();
    let v = valid
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let op = unit.methods.get("valid").expect("valid method not found!");
    let valid_body = op.body.as_ref().unwrap();

    let mut state_refs = HashSet::new();
    valid_body.get_state_references(&mut state_refs);

    let iface = &unit.interface;

    let mut vars = HashMap::new();
    vars.insert("$unit", v.clone());

    let state = &unit.state;
    for sref in &state_refs {
        let val = iface
            .read_state_expr(sref, state.get_field_range(sref))
            .unwrap();

        let sref_var_name = format!("{}_val", sref.replace('.', "_"));

        let sref_var = valid
            .body()
            .new_variable(sref_var_name.as_str(), C::Type::new_uint64())
            .to_expr();

        valid
            .body()
            .assign(sref_var.clone(), unit.expr_to_cpp(&vars, &val));

        vars.insert(sref.as_str(), sref_var);
    }

    valid
        .body()
        .return_expr(unit.expr_to_cpp(&vars, valid_body));

    scope.push_function(valid);
}

fn add_op_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    op: &VelosiAstMethod,
    has_children: bool,
) {
    // declare the function
    let mut fun = C::Function::with_string(
        if has_children {
            unit.to_op_fn_name_table(op)
        } else {
            unit.to_op_fn_name(op)
        },
        C::Type::new_size(),
    );
    fun.set_static().set_inline();

    // add the parameters
    let mut field_vars = HashMap::new();

    let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
    field_vars.insert(String::from("unit"), v.to_expr());

    for f in op.params.iter() {
        let _p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
    }

    if op.requires.is_empty() {
        fun.body().new_comment("no requires clauses");
    } else {
        fun.body().new_comment("asserts for the requires clauses");
    }
    for r in op.requires.iter() {
        // add asserts!
        let vars = HashMap::new();
        fun.body()
            .fn_call("assert", vec![unit.expr_to_cpp(&vars, r)]);
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
                let field_type = f.to_type_name(unit);

                let var = fun
                    .body()
                    .new_variable(field, C::Type::new_typedef(&field_type));

                let fncall_name = f.to_set_val_fn(unit);
                var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
                field_vars.insert(field.clone(), var.to_expr());
            }
        }

        fun.body().new_comment("configuration sequence");
        for op in &op.ops {
            utils::op_to_c_expr(unit.ident(), fun.body(), op, &field_vars);
        }

        let page_size: u64 = 1 << unit.inbitwidth;
        fun.body().return_expr(C::Expr::new_num(page_size));
    } else {
        fun.body().new_comment("there is no configuration sequence");
        fun.body().return_expr(C::Expr::new_num(0));
    }

    scope.push_function(fun);
}

fn add_map_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let m_fn = unit.get_method("map").unwrap();
    add_op_fn(scope, unit, m_fn, false);
}

fn add_unmap_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, has_children: bool) {
    let m_fn = unit.get_method("unmap").unwrap();
    add_op_fn(scope, unit, m_fn, has_children);
}

fn add_protect_function(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, has_children: bool) {
    let m_fn = unit.get_method("protect").unwrap();
    add_op_fn(scope, unit, m_fn, has_children);
}

fn add_higher_order_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    op: &VelosiAstMethod,
    child: &VelosiAstUnit,
) {
    // declare the function
    let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
    fun.set_static().set_inline();

    // add the parameters
    let mut param_exprs = HashMap::new();

    let v = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("unit", v.clone());
    for f in op.params.iter() {
        let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    let mut args = vec![C::Expr::fn_call(&unit.resolve_fn_name(), vec![v.clone()])];
    args.extend(
        op.params
            .iter()
            .map(|param| param_exprs[param.ident().as_str()].clone()),
    );

    fun.body()
        .return_expr(C::Expr::fn_call(&child.to_op_fn_name(op), args));

    scope.push_function(fun);
}

fn add_resolve_fn(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, child: &VelosiAstUnit) {
    // add the translate function as a helper
    let op = unit
        .methods
        .get("translate")
        .expect("map method not found!");

    let mut translate =
        C::Function::with_string(unit.translate_fn_name(), C::Type::new_typedef("paddr_t"));
    translate.set_static().set_inline();

    let mut vars = HashMap::new();
    let v = translate
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    vars.insert("unit", v.clone());
    for f in op.params.iter() {
        let p = translate.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        vars.insert(f.ident().as_str(), p.to_expr());
    }

    let translate_body = op.body.as_ref().unwrap();

    let mut state_refs = HashSet::new();
    translate_body.get_state_references(&mut state_refs);

    let iface = &unit.interface;

    vars.insert("$unit", v.clone());

    let state = &unit.state;
    for sref in &state_refs {
        let val = iface
            .read_state_expr(sref, state.get_field_range(sref))
            .unwrap();

        let sref_var_name = format!("{}_val", sref.replace('.', "_"));

        let sref_var = translate
            .body()
            .new_variable(sref_var_name.as_str(), C::Type::new_uint64())
            .to_expr();

        translate
            .body()
            .assign(sref_var.clone(), unit.expr_to_cpp(&vars, &val));

        vars.insert(sref.as_str(), sref_var);
    }

    translate
        .body()
        .return_expr(unit.expr_to_cpp(&vars, translate_body));

    scope.push_function(translate);

    // add resolve
    let mut resolve = C::Function::with_string(unit.resolve_fn_name(), child.to_ctype());
    resolve.set_static().set_inline();

    let v = resolve
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let paddr = C::Expr::fn_call(&unit.translate_fn_name(), vec![v, C::Expr::new_num(0)]);
    resolve
        .body()
        .return_expr(C::Expr::fn_call(&child.constructor_fn_name(), vec![paddr]));

    scope.push_function(resolve);
}

/// generates the VelosiAstUnitSegment definitions
pub fn generate(
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating segment unit {}", unit.ident());

    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // add the header comments
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_include("interface.h", false);

    // add the definitions
    add_unit_constants(s, unit);
    add_unit_flags(s, unit);
    add_constructor_function(s, unit);
    add_map_function(s, unit);

    let has_children = relations.0.get(unit.ident()).is_some();
    add_unmap_function(s, unit, has_children);
    add_protect_function(s, unit, has_children);

    add_valid_fn(s, unit);
    // add_translate_function(s, unit);

    if let Some(children) = relations.0.get(unit.ident()) {
        if !children.is_empty() {
            let child = &children[0];

            // resolve function
            add_resolve_fn(s, unit, child);

            // higher-order unmap and protect
            let op = unit.methods.get("unmap").expect("unmap method not found!");
            add_higher_order_fn(s, unit, op, child);

            let op = unit
                .methods
                .get("protect")
                .expect("protect method not found!");
            add_higher_order_fn(s, unit, op, child);
        }
    }

    log::debug!("saving the scope!");
    // save the scope
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;

    Ok(())
}
