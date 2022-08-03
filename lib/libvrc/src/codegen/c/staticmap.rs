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

//! StaticMap Generation (C)

use std::collections::HashMap;
use std::path::Path;

use crustal as C;

use super::utils;
use crate::ast::{AstNodeGeneric, ExplicitMap, Expr, ListComprehensionMap, Map, StaticMap};
use crate::codegen::CodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &StaticMap) {
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

// /// adds the struct definition of the unit to the scope
// fn add_struct_definition(scope: &mut C::Scope, unit: &Unit) {
//     // a field is a struct
//     //
//     // field_name  --> struct FieldName {  val: u64 };

//     // create the struct in the scope
//     let st = scope.new_struct(unit.name());

//     // make it public
//     st.vis("pub");

//     // add the doc field to the struct
//     st.doc(&format!(
//         "Represents the Unit type '{}'.\n@loc: {}",
//         unit.name(),
//         unit.location()
//     ));

//     // it has a single field, called 'val'
//     //st.field("val", to_rust_type(field.nbits()));
// }

fn add_constructor_function(scope: &mut C::Scope, unit: &StaticMap) {
    let fname = utils::constructor_fn_name(unit.name());

    let unittype = C::Type::new_typedef(&utils::unit_type_name(unit.name()));

    let mut fun = C::Function::with_string(fname, unittype.clone());
    fun.set_static().set_inline();

    let mut params = Vec::new();
    for p in &unit.params {
        let param = fun.new_param(p.name(), C::Type::new_uint64()).to_expr();
        params.push((&p.name, param));
    }

    let body = fun.body();

    let unittype = C::Type::new_typedef(&utils::unit_type_name(&unit.name));
    let tunit = body.new_variable("targetunit", unittype).to_expr();

    for (name, p) in params {
        let n = utils::unit_struct_field_name(name);
        body.assign(C::Expr::field_access(&tunit, &n), p);
    }

    body.return_expr(tunit);

    scope.push_function(fun);
}

fn add_list_comp_translate_body(
    scope: &mut C::Block,
    lcm: &ListComprehensionMap,
    unit: &StaticMap,
) {
    let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

    let mname = utils::translate_fn_name(&lcm.entry.unit_name);
    scope.new_comment("4) resolve(u, targetva);");

    scope.return_expr(C::Expr::fn_call(
        &mname,
        vec![
            C::Expr::addr_of(&tunit),
            targetva,
            // C::Expr::new_var("size", C::Type::new_uint64()),
            // C::Expr::new_var("pa", C::Type::new_uint64()),
            // C::Expr::new_var("flags", C::Type::new_uint64()),
        ],
    ));

    scope.new_comment("5) todo: handle loops?");
}

fn add_explicit_translate_body(scope: &mut C::Block, _lcm: &ExplicitMap, _unit: &StaticMap) {
    scope.new_comment("1) find which entry to read...");

    scope.new_comment("2) construct the state pointer of the entry...");

    scope.new_comment("3) construct the new address to map");

    scope.new_comment("4) call translate");
}

fn add_translate_function(scope: &mut C::Scope, unit: &StaticMap) {
    let fname = utils::translate_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    // fun.new_param("size", C::Type::new_size());
    fun.new_param("pa", C::Type::new_uint64().to_ptr());

    // fun.new_param("flags", C::Type::new_int(64));

    match &unit.map {
        Some(Map::Explicit(m)) => add_explicit_translate_body(fun.body(), m, unit),
        Some(Map::ListComprehension(m)) => add_list_comp_translate_body(fun.body(), m, unit),
        None => (),
    }

    scope.push_function(fun);
}

fn ast_expr_to_c_expr(e: &Expr) -> C::Expr {
    match e {
        Expr::Identifier { path, .. } => C::Expr::new_var(&path.join("."), C::Type::new_int64()),
        Expr::Number { value, .. } => C::Expr::new_num(*value),
        Expr::BinaryOperation { op, lhs, rhs, .. } => C::Expr::binop(
            ast_expr_to_c_expr(lhs),
            &op.to_string(),
            ast_expr_to_c_expr(rhs),
        ),
        _ => panic!("expression not handled yet\n"),
    }
}

fn generic_list_comp_body(
    scope: &mut C::Block,
    lcm: &ListComprehensionMap,
    unit: &StaticMap,
) -> (C::Expr, C::Expr) {
    if lcm.entry.range.is_some() {
        panic!("having ranges its not yet supported here...\n");
    }

    // get the size of the unit, hardcode to 4k for now..
    // TODO: we need to get the size of the unit from somewhere, maybe add the
    // symbol table here?
    let unitsize = 4096;

    for p in &unit.params {
        let var = scope.new_variable(&p.name, C::Type::new_int64()).to_expr();
        scope.assign(
            var,
            C::Expr::field_access(
                &C::Expr::new_var("unit", C::Type::new_void().to_ptr()),
                &utils::unit_struct_field_name(&p.name),
            ),
        );
    }

    let vavar = C::Expr::new_var("va", C::Type::new_int64());
    let num_entries = lcm.get_range_max();
    let maxaddr = num_entries * unitsize;
    scope.new_comment("we can't handle addresses higher than this");
    scope.fn_call(
        "assert",
        vec![C::Expr::binop(
            vavar.clone(),
            "<",
            C::Expr::new_num(maxaddr),
        )],
    );

    // get the field from the unit
    //let field_type = utils::field_type_name(unit, &f.field);

    let entry = scope.new_variable(&lcm.var, C::Type::new_int64()).to_expr();
    let targetva = scope
        .new_variable("targetva", C::Type::new_int64())
        .to_expr();

    scope.new_comment("1) entry: va / unitsize");
    scope.assign(
        entry.clone(),
        C::Expr::binop(vavar.clone(), "/", C::Expr::new_num(unitsize)),
    );

    scope.fn_call(
        "assert",
        vec![C::Expr::binop(entry, "<", C::Expr::new_num(num_entries))],
    );

    scope.new_comment("2) targetva = va - entry offset + target offset");
    scope.assign(
        targetva.clone(),
        C::Expr::binop(vavar, "%", C::Expr::new_num(unitsize)),
    );

    if let Some(_offset) = &lcm.entry.offset {
        scope.new_comment("adding offset to the virtual address");
        //scope.assign(targetva.clone(), C::Expr::binop(targetva.clone(), "=", C::Expr::new_num(offset)));
        panic!("adding expressions is not yet supported.");
    } else {
        scope.new_comment("there is no offset into the unit..");
    }

    scope.new_comment("3) construct the state pointer of the entry...");
    let mut fnargs = Vec::new();
    for (i, u) in lcm.entry.unit_params.iter().enumerate() {
        let argname = format!("arg{}", i);
        let targetbase = scope.new_variable(&argname, C::Type::new_int64()).to_expr();
        scope.assign(targetbase.clone(), ast_expr_to_c_expr(u));

        fnargs.push(targetbase);
    }

    let cname = utils::constructor_fn_name(&lcm.entry.unit_name);

    let unittype = C::Type::new_typedef(&utils::unit_type_name(&lcm.entry.unit_name));
    let tunit = scope.new_variable("targetunit", unittype).to_expr();

    scope.assign(tunit.clone(), C::Expr::fn_call(&cname, fnargs));

    (tunit, targetva)
}

fn add_list_comp_map_body(scope: &mut C::Block, lcm: &ListComprehensionMap, unit: &StaticMap) {
    let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

    let mname = utils::map_fn_name(&lcm.entry.unit_name);
    scope.new_comment("4) x86pagetableentry_map(u, targetva, size, pa, flags);");
    scope.fn_call(
        &mname,
        vec![
            C::Expr::addr_of(&tunit),
            targetva,
            C::Expr::new_var("size", C::Type::new_uint64()),
            C::Expr::new_var("pa", C::Type::new_uint64()),
            C::Expr::new_var("flags", C::Type::new_uint64()),
        ],
    );

    scope.new_comment("5) todo: handle loops?");
}

fn add_explicit_map_body(scope: &mut C::Block, _lcm: &ExplicitMap, _unit: &StaticMap) {
    scope.new_comment("1) find which entry to read...");

    scope.new_comment("2) construct the state pointer of the entry...");

    scope.new_comment("3) construct the new address to map");

    scope.new_comment("4) call map_entry");

    scope.new_comment("5) todo: handle loops?");
}

fn add_map_function(scope: &mut C::Scope, unit: &StaticMap) {
    let fname = utils::map_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    fun.new_param("size", C::Type::new_size());
    fun.new_param("pa", C::Type::new_uint64());
    fun.new_param("flags", C::Type::new_int(64));

    match &unit.map {
        Some(Map::Explicit(m)) => add_explicit_map_body(fun.body(), m, unit),
        Some(Map::ListComprehension(m)) => add_list_comp_map_body(fun.body(), m, unit),
        None => (),
    }

    fun.body().new_return(Some(&C::Expr::btrue()));

    scope.push_function(fun);
}

fn add_list_comp_unmap_body(scope: &mut C::Block, lcm: &ListComprehensionMap, unit: &StaticMap) {
    let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

    let mname = utils::unmap_fn_name(&lcm.entry.unit_name);
    scope.new_comment("4) x86pagetableentry_unmap(u, targetva, size, pa, flags);");
    scope.fn_call(
        &mname,
        vec![
            C::Expr::addr_of(&tunit),
            targetva,
            C::Expr::new_var("size", C::Type::new_uint64()),
        ],
    );

    scope.new_comment("5) todo: handle loops?");
}

fn add_explicit_unmap_body(scope: &mut C::Block, _lcm: &ExplicitMap, _unit: &StaticMap) {
    scope.new_comment("1) find which entry to read...");

    scope.new_comment("2) construct the state pointer of the entry...");

    scope.new_comment("3) construct the new address to map");

    scope.new_comment("4) call map_entry");

    scope.new_comment("5) todo: handle loops?");
}

fn add_unmap_function(scope: &mut C::Scope, unit: &StaticMap) {
    let fname = utils::unmap_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    fun.new_param("size", C::Type::new_size());

    match &unit.map {
        Some(Map::Explicit(m)) => add_explicit_unmap_body(fun.body(), m, unit),
        Some(Map::ListComprehension(m)) => add_list_comp_unmap_body(fun.body(), m, unit),
        None => (),
    }

    fun.body().new_return(Some(&C::Expr::btrue()));

    scope.push_function(fun);
}

fn add_list_comp_protect_body(scope: &mut C::Block, lcm: &ListComprehensionMap, unit: &StaticMap) {
    let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

    let mname = utils::protect_fn_name(&lcm.entry.unit_name);
    scope.new_comment("4) x86pagetableentry_protect(u, targetva, size, pa, flags);");
    scope.fn_call(
        &mname,
        vec![
            C::Expr::addr_of(&tunit),
            targetva,
            C::Expr::new_var("size", C::Type::new_uint64()),
            C::Expr::new_var("flags", C::Type::new_uint64()),
        ],
    );

    scope.new_comment("5) todo: handle loops?");
}

fn add_explicit_protect_body(scope: &mut C::Block, _lcm: &ExplicitMap, _unit: &StaticMap) {
    scope.new_comment("1) find which entry to read...");

    scope.new_comment("2) construct the state pointer of the entry...");

    scope.new_comment("3) construct the new address to map");

    scope.new_comment("4) call map_entry");

    scope.new_comment("5) todo: handle loops?");
}

fn add_protect_function(scope: &mut C::Scope, unit: &StaticMap) {
    let fname = utils::protect_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    fun.new_param("size", C::Type::new_size());
    fun.new_param("flags", C::Type::new_int(64));

    match &unit.map {
        Some(Map::Explicit(m)) => add_explicit_protect_body(fun.body(), m, unit),
        Some(Map::ListComprehension(m)) => add_list_comp_protect_body(fun.body(), m, unit),
        None => (),
    }

    fun.body().new_return(Some(&C::Expr::btrue()));

    scope.push_function(fun);
}

fn generate_unit_struct(scope: &mut C::Scope, unit: &StaticMap) {
    let fields = unit
        .params
        .iter()
        .map(|x| {
            let n = utils::unit_struct_field_name(&x.name);
            C::Field::with_string(n, C::Type::new_uintptr())
        })
        .collect();

    let sn = utils::staticmap_struct_name(unit);
    let mut s = C::Struct::with_fields(&sn, fields);

    s.push_doc_str(&format!("Unit Type `{}`", unit.name));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.pos.location()));

    let stype = s.to_type();

    scope.push_struct(s);

    // adding a type def;
    let fieldtype = utils::staticmap_type_name(unit);
    scope.new_typedef(&fieldtype, stype);
}

/// generates the Segment definitions
pub fn generate(unit: &StaticMap, outdir: &Path) -> Result<(), CodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.name());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.name().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.name());
    utils::add_header(s, &title);

    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    // find all the used other units in the static map
    if let Some(m) = &unit.map {
        s.new_comment("include refernces to the used units");
        for u in m.get_unit_names().iter() {
            let path = format!("../{}/unit.h", u.to_ascii_lowercase());
            s.new_include(&path, false);
        }
    } else {
        panic!("we don't have a mpa construct set\n");
    }

    // add the definitions
    add_unit_constants(s, unit);
    generate_unit_struct(s, unit);
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
