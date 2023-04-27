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

use velosiast::{
    VelosiAst, VelosiAstMethod, VelosiAstStaticMap, VelosiAstStaticMapListComp,
    VelosiAstUnitStaticMap,
};

use super::utils::{self, UnitUtils};
use crate::VelosiCodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in unit.consts.values() {
        utils::add_const_def(scope, c);
    }
}

fn add_unit_flags(_scope: &mut C::Scope, _unit: &VelosiAstUnitStaticMap) {

    // TODO: add the flags as a union of all other units this one maps to?
}

// // /// adds the struct definition of the unit to the scope
// // fn add_struct_definition(scope: &mut C::Scope, unit: &Unit) {
// //     // a field is a struct
// //     //
// //     // field_name  --> struct FieldName {  val: u64 };

// //     // create the struct in the scope
// //     let st = scope.new_struct(unit.ident());

// //     // make it public
// //     st.vis("pub");

// //     // add the doc field to the struct
// //     st.doc(&format!(
// //         "Represents the Unit type '{}'.\n@loc: {}",
// //         unit.ident(),
// //         unit.location()
// //     ));

// //     // it has a single field, called 'val'
// //     //st.field("val", to_rust_type(field.nbits()));
// // }

// fn add_list_comp_translate_body(
//     scope: &mut C::Block,
//     lcm: &VelosiAstStaticMapListComp,
//     unit: &VelosiAstUnitStaticMap,
// ) {
//     let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

//     let mname = utils::translate_fn_name(lcm.elm.dst.ident());
//     scope.new_comment("4) resolve(u, targetva);");

//     scope.return_expr(C::Expr::fn_call(
//         &mname,
//         vec![
//             C::Expr::addr_of(&tunit),
//             targetva,
//             // C::Expr::new_var("size", C::Type::new_uint64()),
//             // C::Expr::new_var("pa", C::Type::new_uint64()),
//             // C::Expr::new_var("flags", C::Type::new_uint64()),
//         ],
//     ));

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_explicit_translate_body(
//     scope: &mut C::Block,
//     _lcm: &VelosiAstStaticMapExplicit,
//     _unit: &VelosiAstUnitStaticMap,
// ) {
//     scope.new_comment("1) find which entry to read...");

//     scope.new_comment("2) construct the state pointer of the entry...");

//     scope.new_comment("3) construct the new address to map");

//     scope.new_comment("4) call translate");
// }

// fn add_translate_function(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
//     let fname = utils::translate_fn_name(unit.ident());

//     let mut fun = C::Function::with_string(fname, C::Type::new_bool());
//     fun.set_static().set_inline();

//     let mut field_vars = HashMap::new();
//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.ident())));

//     let v = fun.new_param("unit", unittype);
//     field_vars.insert(String::from("unit"), v.to_expr());
//     fun.new_param("va", C::Type::new_uint64());
//     // fun.new_param("size", C::Type::new_size());
//     fun.new_param("pa", C::Type::new_uint64().to_ptr());

//     // fun.new_param("flags", C::Type::new_int(64));

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(m) => add_explicit_translate_body(fun.body(), m, unit),
//         VelosiAstStaticMap::ListComp(m) => add_list_comp_translate_body(fun.body(), m, unit),
//         _ => (),
//     }

//     scope.push_function(fun);
// }

// fn ast_expr_to_c_expr(e: &Expr) -> C::Expr {
//     match e {
//         Expr::Identifier { path, .. } => C::Expr::new_var(&path.join("."), C::Type::new_int64()),
//         Expr::Number { value, .. } => C::Expr::new_num(*value),
//         Expr::BinaryOperation { op, lhs, rhs, .. } => C::Expr::binop(
//             ast_expr_to_c_expr(lhs),
//             &op.to_string(),
//             ast_expr_to_c_expr(rhs),
//         ),
//         _ => panic!("expression not handled yet\n"),
//     }
// }

// fn generic_list_comp_body(
//     scope: &mut C::Block,
//     lcm: &VelosiAstStaticMapListComp,
//     unit: &VelosiAstUnitStaticMap,
// ) -> (C::Expr, C::Expr) {
//     if lcm.entry.range.is_some() {
//         panic!("having ranges its not yet supported here...\n");
//     }

//     // get the size of the unit, hardcode to 4k for now..
//     // TODO: we need to get the size of the unit from somewhere, maybe add the
//     // symbol table here?
//     let unitsize = 4096;

//     for p in &unit.params {
//         let var = scope
//             .new_variable(p.ident(), C::Type::new_int64())
//             .to_expr();
//         scope.assign(
//             var,
//             C::Expr::field_access(
//                 &C::Expr::new_var("unit", C::Type::new_void().to_ptr()),
//                 &utils::unit_struct_field_name(p.ident()),
//             ),
//         );
//     }

//     let vavar = C::Expr::new_var("va", C::Type::new_int64());
//     let num_entries = lcm.get_range_max();
//     let maxaddr = num_entries * unitsize;
//     scope.new_comment("we can't handle addresses higher than this");
//     scope.fn_call(
//         "assert",
//         vec![C::Expr::binop(
//             vavar.clone(),
//             "<",
//             C::Expr::new_num(maxaddr),
//         )],
//     );

//     // get the field from the unit
//     //let field_type = utils::field_type_name(unit, &f.field);

//     let entry = scope
//         .new_variable(lcm.var.ident(), C::Type::new_int64())
//         .to_expr();
//     let targetva = scope
//         .new_variable("targetva", C::Type::new_int64())
//         .to_expr();

//     scope.new_comment("1) entry: va / unitsize");
//     scope.assign(
//         entry.clone(),
//         C::Expr::binop(vavar.clone(), "/", C::Expr::new_num(unitsize)),
//     );

//     scope.fn_call(
//         "assert",
//         vec![C::Expr::binop(entry, "<", C::Expr::new_num(num_entries))],
//     );

//     scope.new_comment("2) targetva = va - entry offset + target offset");
//     scope.assign(
//         targetva.clone(),
//         C::Expr::binop(vavar, "%", C::Expr::new_num(unitsize)),
//     );

//     if let Some(_offset) = &lcm.elm.offset {
//         scope.new_comment("adding offset to the virtual address");
//         //scope.assign(targetva.clone(), C::Expr::binop(targetva.clone(), "=", C::Expr::new_num(offset)));
//         panic!("adding expressions is not yet supported.");
//     } else {
//         scope.new_comment("there is no offset into the unit..");
//     }

//     scope.new_comment("3) construct the state pointer of the entry...");
//     let mut fnargs = Vec::new();
//     for (i, u) in lcm.elm.dst.args.iter().enumerate() {
//         let argname = format!("arg{}", i);
//         let targetbase = scope.new_variable(&argname, C::Type::new_int64()).to_expr();
//         scope.assign(targetbase.clone(), ast_expr_to_c_expr(u));

//         fnargs.push(targetbase);
//     }

//     let cname = utils::constructor_fn_name(lcm.elm.dst.ident());

//     let unittype = C::Type::new_typedef(&utils::unit_type_name(lcm.elm.dst.ident()));
//     let tunit = scope.new_variable("targetunit", unittype).to_expr();

//     scope.assign(tunit.clone(), C::Expr::fn_call(&cname, fnargs));

//     (tunit, targetva)
// }

// fn add_list_comp_map_body(
//     scope: &mut C::Block,
//     lcm: &VelosiAstStaticMapListComp,
//     unit: &VelosiAstUnitStaticMap,
// ) {
//     let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

//     let mname = utils::map_fn_name(lcm.elm.dst.ident());
//     scope.new_comment("4) x86pagetableentry_map(u, targetva, size, pa, flags);");
//     scope.fn_call(
//         &mname,
//         vec![
//             C::Expr::addr_of(&tunit),
//             targetva,
//             C::Expr::new_var("size", C::Type::new_uint64()),
//             C::Expr::new_var("pa", C::Type::new_uint64()),
//             C::Expr::new_var("flags", C::Type::new_uint64()),
//         ],
//     );

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_explicit_map_body(
//     scope: &mut C::Block,
//     _lcm: &VelosiAstStaticMapExplicit,
//     _unit: &VelosiAstUnitStaticMap,
// ) {
//     scope.new_comment("1) find which entry to read...");

//     scope.new_comment("2) construct the state pointer of the entry...");

//     scope.new_comment("3) construct the new address to map");

//     scope.new_comment("4) call map_entry");

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_map_function(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
//     let fname = utils::map_fn_name(unit.ident());

//     let mut fun = C::Function::with_string(fname, C::Type::new_bool());
//     fun.set_static().set_inline();

//     let mut field_vars = HashMap::new();
//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.ident())));

//     let v = fun.new_param("unit", unittype);
//     field_vars.insert(String::from("unit"), v.to_expr());
//     fun.new_param("va", C::Type::new_uint64());
//     fun.new_param("size", C::Type::new_size());
//     fun.new_param("pa", C::Type::new_uint64());
//     fun.new_param("flags", C::Type::new_int(64));

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(m) => add_explicit_map_body(fun.body(), m, unit),
//         VelosiAstStaticMap::ListComp(m) => add_list_comp_map_body(fun.body(), m, unit),
//         _ => (),
//     }

//     fun.body().new_return(Some(&C::Expr::btrue()));

//     scope.push_function(fun);
// }

// fn add_list_comp_unmap_body(
//     scope: &mut C::Block,
//     lcm: &VelosiAstStaticMapListComp,
//     unit: &VelosiAstUnitStaticMap,
// ) {
//     let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

//     let mname = utils::unmap_fn_name(lcm.elm.dst.ident());
//     scope.new_comment("4) x86pagetableentry_unmap(u, targetva, size, pa, flags);");
//     scope.fn_call(
//         &mname,
//         vec![
//             C::Expr::addr_of(&tunit),
//             targetva,
//             C::Expr::new_var("size", C::Type::new_uint64()),
//         ],
//     );

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_explicit_unmap_body(
//     scope: &mut C::Block,
//     _lcm: &VelosiAstStaticMapExplicit,
//     _unit: &VelosiAstUnitStaticMap,
// ) {
//     scope.new_comment("1) find which entry to read...");

//     scope.new_comment("2) construct the state pointer of the entry...");

//     scope.new_comment("3) construct the new address to map");

//     scope.new_comment("4) call map_entry");

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_unmap_function(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
//     let fname = utils::unmap_fn_name(unit.ident());

//     let mut fun = C::Function::with_string(fname, C::Type::new_bool());
//     fun.set_static().set_inline();

//     let mut field_vars = HashMap::new();
//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.ident())));

//     let v = fun.new_param("unit", unittype);
//     field_vars.insert(String::from("unit"), v.to_expr());
//     fun.new_param("va", C::Type::new_uint64());
//     fun.new_param("size", C::Type::new_size());

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(m) => add_explicit_unmap_body(fun.body(), m, unit),
//         VelosiAstStaticMap::ListComp(m) => add_list_comp_unmap_body(fun.body(), m, unit),
//         _ => (),
//     }

//     fun.body().new_return(Some(&C::Expr::btrue()));

//     scope.push_function(fun);
// }

// fn add_list_comp_protect_body(
//     scope: &mut C::Block,
//     lcm: &VelosiAstStaticMapListComp,
//     unit: &VelosiAstUnitStaticMap,
// ) {
//     let (tunit, targetva) = generic_list_comp_body(scope, lcm, unit);

//     let mname = utils::protect_fn_name(lcm.elm.dst.ident());
//     scope.new_comment("4) x86pagetableentry_protect(u, targetva, size, pa, flags);");
//     scope.fn_call(
//         &mname,
//         vec![
//             C::Expr::addr_of(&tunit),
//             targetva,
//             C::Expr::new_var("size", C::Type::new_uint64()),
//             C::Expr::new_var("flags", C::Type::new_uint64()),
//         ],
//     );

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_explicit_protect_body(
//     scope: &mut C::Block,
//     _lcm: &VelosiAstStaticMapExplicit,
//     _unit: &VelosiAstUnitStaticMap,
// ) {
//     scope.new_comment("1) find which entry to read...");

//     scope.new_comment("2) construct the state pointer of the entry...");

//     scope.new_comment("3) construct the new address to map");

//     scope.new_comment("4) call map_entry");

//     scope.new_comment("5) todo: handle loops?");
// }

// fn add_protect_function(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
//     let fname = utils::protect_fn_name(unit.ident());

//     let mut fun = C::Function::with_string(fname, C::Type::new_bool());
//     fun.set_static().set_inline();

//     let mut field_vars = HashMap::new();
//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.ident())));

//     let v = fun.new_param("unit", unittype);
//     field_vars.insert(String::from("unit"), v.to_expr());
//     fun.new_param("va", C::Type::new_uint64());
//     fun.new_param("size", C::Type::new_size());
//     fun.new_param("flags", C::Type::new_int(64));

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(m) => add_explicit_protect_body(fun.body(), m, unit),
//         VelosiAstStaticMap::ListComp(m) => add_list_comp_protect_body(fun.body(), m, unit),
//         _ => (),
//     }

//     fun.body().new_return(Some(&C::Expr::btrue()));

//     scope.push_function(fun);
// }

fn add_op_fn_body_listcomp(
    scope: &mut C::Block,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
    mut params_exprs: HashMap<&str, C::Expr>,
) {
    scope.new_comment(map.to_string().as_str());

    let idx_var = scope.new_variable("idx", C::Type::new_size()).to_expr();

    let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
    let va_var = params_exprs.get("va").unwrap();

    // idx = va / element_size
    scope.assign(
        idx_var.clone(),
        C::Expr::binop(
            va_var.clone(),
            ">>",
            C::Expr::ConstNum(dest_unit.input_bitwidth()),
        ),
    );

    // va = va & (element_size - 1)
    scope.assign(
        va_var.clone(),
        C::Expr::binop(
            va_var.clone(),
            "&",
            C::Expr::binop(
                C::Expr::binop(
                    C::Expr::ConstNum(1),
                    "<<",
                    C::Expr::ConstNum(dest_unit.input_bitwidth()),
                ),
                "-",
                C::Expr::ConstNum(1),
            ),
        ),
    );

    // nee d

    let tunit = scope
        .new_variable("targetunit", dest_unit.to_ctype())
        .to_expr();

    let unit_var = params_exprs.get("unit").unwrap();
    let mut var_mappings = HashMap::new();
    for p in unit.params_as_slice() {
        var_mappings.insert(
            p.ident().as_str(),
            C::Expr::field_access(unit_var, p.ident().as_str()),
        );
    }

    var_mappings.insert(map.var.ident().as_str(), idx_var);

    // TODO here!
    let args = map
        .elm
        .dst
        .args
        .iter()
        .map(|p| unit.expr_to_cpp(&var_mappings, p))
        .collect();

    scope.assign(
        tunit.clone(),
        C::Expr::fn_call(&dest_unit.constructor_fn_name(), args),
    );

    let mut args = vec![C::Expr::addr_of(&tunit)];
    for arg in op.params.iter() {
        let e = params_exprs.remove(arg.ident().as_str()).unwrap();
        args.push(e);
    }
    scope.return_expr(C::Expr::fn_call(&dest_unit.to_op_fn_name(op), args));
}

fn add_op_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    op: &VelosiAstMethod,
) {
    // declare the function
    let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_bool());
    fun.set_static().set_inline();

    let mut param_exprs = HashMap::new();

    let v = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("unit", v);
    for f in op.params.iter() {
        let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    // todo: add requires

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            fun.body().new_comment("TODO: Explicit map");
        }
        VelosiAstStaticMap::ListComp(map) => {
            add_op_fn_body_listcomp(fun.body(), ast, unit, map, op, param_exprs);
        }
        VelosiAstStaticMap::None(_) => {
            fun.body().new_comment("No map defined for this unit");
        }
    }

    // push the function to the scope
    scope.push_function(fun);
}

fn add_op_functions(scope: &mut C::Scope, ast: &VelosiAst, unit: &VelosiAstUnitStaticMap) {
    let op = unit.methods.get("map").expect("unmap method not found!");
    add_op_function(scope, ast, unit, op);
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_function(scope, ast, unit, op);
    let op = unit
        .methods
        .get("protect")
        .expect("unmap method not found!");
    add_op_function(scope, ast, unit, op);
}

fn generate_unit_struct(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
    let fields = unit
        .params
        .iter()
        .map(|x| C::Field::with_string(x.ident().to_string(), C::Type::new_uintptr()))
        .collect();

    let mut s = C::Struct::with_fields(&unit.to_struct_name(), fields);

    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

    let stype = s.to_type();

    // add the struct definition to the scope
    scope.push_struct(s);

    // add the type def to the scope
    scope.new_typedef(&unit.to_type_name(), stype);
}

fn add_constructor_function(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
    let mut fun = C::Function::with_string(unit.constructor_fn_name(), unit.to_ctype());
    fun.set_static().set_inline();

    let mut params = Vec::new();
    for p in &unit.params {
        let param = fun.new_param(p.ident(), C::Type::new_uint64()).to_expr();
        params.push((p.ident(), param));
    }

    let body = fun.body();

    let unittype = unit.to_ctype();
    let tunit = body.new_variable("targetunit", unittype).to_expr();

    for (name, p) in params {
        body.assign(C::Expr::field_access(&tunit, name), p);
    }

    body.return_expr(tunit);

    scope.push_function(fun);
}

/// generates the staticmap definitions
pub fn generate(
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating staticmap unit {}", unit.ident());

    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // add the header comments
    let _title = format!("`{}` Unit definition ", unit.ident());

    // add systems include
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    // find all the used other units in the static map
    s.new_comment("include refernces to the used units");
    for u in unit.map.get_unit_names().iter() {
        let path = format!("../{}/unit.h", u.to_ascii_lowercase());
        s.new_include(&path, false);
    }

    // add the definitions
    add_unit_constants(s, unit);
    add_unit_flags(s, unit);
    generate_unit_struct(s, unit);
    add_constructor_function(s, unit);
    add_op_functions(s, ast, unit);

    // add_translate_function(s, unit);

    // save the scope
    log::debug!("saving the scope!");
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;
    Ok(())
}
