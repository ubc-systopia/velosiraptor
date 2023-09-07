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

use std::path::Path;
use std::{collections::HashMap, rc::Rc};

use crustal as C;

use velosiast::{
    VelosiAst, VelosiAstMethod, VelosiAstStaticMap, VelosiAstStaticMapListComp, VelosiAstUnit,
    VelosiAstUnitStaticMap,
};
use velosicomposition::Relations;

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

fn base_inbitwidth(relations: &Relations, ident: &Rc<String>, inbitwidth: u64) -> u64 {
    if let Some(units) = relations.0.get(ident) {
        units
            .iter()
            .map(|u| base_inbitwidth(relations, u.ident(), u.input_bitwidth()))
            .chain(std::iter::once(inbitwidth))
            .min()
            .unwrap()
    } else {
        inbitwidth
    }
}

fn add_higher_order_map(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
) {
    let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(map) => {
            let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
            match dest_unit {
                VelosiAstUnit::Enum(e) => {
                    let op = unit.get_method("map").unwrap();

                    let mut fun =
                        C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
                    fun.set_static().set_inline();

                    let mut param_exprs = HashMap::new();

                    let v = fun
                        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                        .to_expr();
                    param_exprs.insert("unit", v.clone());
                    for f in op.params.iter() {
                        let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
                        param_exprs.insert(f.ident().as_str(), p.to_expr());
                    }

                    let va = &param_exprs["va"];
                    let sz = &param_exprs["sz"];
                    let pa = &param_exprs["pa"];
                    let body = &mut fun.body();

                    // add assertions
                    for arg in [va, sz, pa] {
                        body.fn_call(
                            "assert",
                            vec![C::Expr::binop(
                                C::Expr::binop(
                                    arg.clone(),
                                    "%",
                                    C::Expr::new_num(base_page_size as u64),
                                ),
                                "==",
                                C::Expr::new_num(0),
                            )],
                        );
                    }

                    let original_sz = body
                        .new_variable("original_sz", C::Type::new_size())
                        .to_expr();
                    body.assign(original_sz.clone(), sz.clone());

                    let (has_children, no_children): (Vec<_>, Vec<_>) = e
                        .get_next_unit_idents()
                        .into_iter()
                        .partition(|variant| relations.0.get(*variant).is_some());

                    for variant in no_children {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let page_size: usize = 1 << variant_unit.input_bitwidth();

                        let mut if_block = C::IfElse::new(&C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(
                                    C::Expr::binop(
                                        va.clone(),
                                        "%",
                                        C::Expr::new_num(page_size as u64),
                                    ),
                                    "==",
                                    C::Expr::new_num(0),
                                ),
                                "&&",
                                C::Expr::binop(
                                    C::Expr::binop(
                                        pa.clone(),
                                        "%",
                                        C::Expr::new_num(page_size as u64),
                                    ),
                                    "==",
                                    C::Expr::new_num(0),
                                ),
                            ),
                            "&&",
                            C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                        ));
                        let i = if_block
                            .then_branch()
                            .new_variable("i", C::Type::new_size())
                            .to_expr();
                        if_block.then_branch().assign(
                            i.clone(),
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(variant_unit.input_bitwidth()),
                            ),
                        );

                        let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(
                                    va.clone(),
                                    ">>",
                                    C::Expr::new_num(variant_unit.input_bitwidth()),
                                ),
                                "==",
                                i,
                            ),
                            "&&",
                            C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                        ));

                        let mut args = Vec::new();
                        for arg in op.params.iter() {
                            if arg.ident().as_str() == "sz" {
                                args.push(C::Expr::new_num(page_size as u64))
                            } else {
                                let e = param_exprs[arg.ident().as_str()].clone();
                                args.push(e);
                            }
                        }

                        while_block
                            .body()
                            .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);
                        while_block.body().assign(
                            sz.clone(),
                            C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
                        );
                        while_block.body().assign(
                            va.clone(),
                            C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
                        );
                        while_block.body().assign(
                            pa.clone(),
                            C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
                        );

                        if_block.then_branch().while_loop(while_block);
                        body.ifelse(if_block);
                    }

                    for variant in &has_children {
                        let children = relations.0.get(*variant).unwrap();
                        let child = &children[0];
                        let variant_unit = ast.get_unit(variant).unwrap();

                        let i = body.new_variable("i", C::Type::new_size()).to_expr();
                        body.assign(
                            i.clone(),
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(variant_unit.input_bitwidth()),
                            ),
                        );

                        let tunit = body
                            .new_variable("targetunit", dest_unit.to_ctype())
                            .to_expr();

                        let unit_var = param_exprs.get("unit").unwrap();
                        let mut var_mappings = HashMap::new();
                        for p in unit.params_as_slice() {
                            var_mappings.insert(
                                p.ident().as_str(),
                                C::Expr::field_access(unit_var, p.ident().as_str()),
                            );
                        }

                        var_mappings.insert(map.var.ident().as_str(), i);

                        let args = map
                            .elm
                            .dst
                            .args
                            .iter()
                            .map(|p| unit.expr_to_cpp(&var_mappings, p))
                            .collect();

                        body.assign(
                            tunit.clone(),
                            C::Expr::fn_call(&dest_unit.constructor_fn_name(), args),
                        );

                        let mut if_block = C::IfElse::new(&C::Expr::uop(
                            "!",
                            C::Expr::fn_call(&dest_unit.valid_fn_name(), vec![tunit.clone()]),
                        ));
                        let child_paddr = if_block
                            .then_branch()
                            .new_variable("child_paddr", C::Type::new_typedef("paddr_t"))
                            .to_expr();
                        if_block.then_branch().assign(
                            child_paddr.clone(),
                            C::Expr::fn_call(
                                "virt_to_phys",
                                vec![C::Expr::fn_call(
                                    "alloc",
                                    vec![C::Expr::new_num(base_page_size as u64)],
                                )],
                            ),
                        );
                        let child_var = if_block
                            .then_branch()
                            .new_variable("child", child.to_ctype())
                            .to_expr();
                        if_block.then_branch().assign(
                            child_var.clone(),
                            C::Expr::fn_call(&child.constructor_fn_name(), vec![child_paddr]),
                        );

                        let mut args = Vec::new();
                        for arg in op.params.iter() {
                            if arg.ident().as_str() == "pa" {
                                args.push(child_var.clone())
                            } else {
                                let e = param_exprs[arg.ident().as_str()].clone();
                                args.push(e);
                            }
                        }

                        if_block
                            .then_branch()
                            .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);

                        body.ifelse(if_block);

                        let child_var = body.new_variable("child", child.to_ctype()).to_expr();

                        body.assign(
                            child_var.clone(),
                            C::Expr::fn_call(
                                &variant_unit.resolve_fn_name(),
                                vec![C::Expr::fn_call(
                                    &variant_unit.constructor_fn_name(),
                                    variant_unit
                                        .params_as_slice()
                                        .iter()
                                        .map(|param| C::Expr::field_access(&tunit, param.ident()))
                                        .collect(),
                                )],
                            ),
                        );
                        let mapped_sz = body
                            .new_variable("mapped_sz", C::Type::new_size())
                            .to_expr();
                        let mut args = vec![C::Expr::addr_of(&child_var)];
                        args.extend(
                            op.params
                                .iter()
                                .map(|param| param_exprs[param.ident().as_str()].clone()),
                        );

                        body.assign(
                            mapped_sz.clone(),
                            C::Expr::fn_call(&child.to_op_fn_name(op), args),
                        );
                        body.assign(
                            sz.clone(),
                            C::Expr::binop(sz.clone(), "-", mapped_sz.clone()),
                        );
                        if variant != has_children.last().unwrap() {
                            body.assign(
                                va.clone(),
                                C::Expr::binop(va.clone(), "+", mapped_sz.clone()),
                            );
                            body.assign(
                                pa.clone(),
                                C::Expr::binop(pa.clone(), "+", mapped_sz.clone()),
                            );
                        }
                    }

                    body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

                    scope.push_function(fun);
                }
                _ => {
                    let op = unit.get_method("map").unwrap();

                    let mut fun =
                        C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
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

                    let va = &param_exprs["va"];
                    let sz = &param_exprs["sz"];
                    let pa = &param_exprs["pa"];
                    let body = &mut fun.body();

                    // add assertions
                    for arg in [va, sz, pa] {
                        body.fn_call(
                            "assert",
                            vec![C::Expr::binop(
                                C::Expr::binop(
                                    arg.clone(),
                                    "%",
                                    C::Expr::new_num(base_page_size as u64),
                                ),
                                "==",
                                C::Expr::new_num(0),
                            )],
                        );
                    }

                    let original_sz = body
                        .new_variable("original_sz", C::Type::new_size())
                        .to_expr();
                    body.assign(original_sz.clone(), sz.clone());
                    let page_size: usize = 1 << dest_unit.input_bitwidth();

                    let mut if_block = C::IfElse::new(&C::Expr::binop(
                        C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(va.clone(), "%", C::Expr::new_num(page_size as u64)),
                                "==",
                                C::Expr::new_num(0),
                            ),
                            "&&",
                            C::Expr::binop(
                                C::Expr::binop(pa.clone(), "%", C::Expr::new_num(page_size as u64)),
                                "==",
                                C::Expr::new_num(0),
                            ),
                        ),
                        "&&",
                        C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                    ));
                    let i = if_block
                        .then_branch()
                        .new_variable("i", C::Type::new_size())
                        .to_expr();
                    if_block.then_branch().assign(
                        i.clone(),
                        C::Expr::binop(
                            va.clone(),
                            ">>",
                            C::Expr::new_num(dest_unit.input_bitwidth()),
                        ),
                    );

                    let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                        C::Expr::binop(
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(dest_unit.input_bitwidth()),
                            ),
                            "==",
                            i,
                        ),
                        "&&",
                        C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                    ));

                    let op = if dest_unit.is_enum() {
                        unit.get_method("map").unwrap()
                    } else {
                        dest_unit.get_method("map").unwrap()
                    };
                    let mut args = Vec::new();
                    for arg in op.params.iter() {
                        if arg.ident().as_str() == "pa" {
                            match &arg.ptype.typeinfo {
                                velosiast::ast::VelosiAstTypeInfo::TypeRef(ty) => {
                                    let child = ast.get_unit(ty).unwrap();
                                    args.push(C::Expr::fn_call(
                                        &child.constructor_fn_name(),
                                        op.params
                                            .iter()
                                            .map(|param| {
                                                param_exprs[param.ident().as_str()].clone()
                                            })
                                            .collect(),
                                    ));
                                }
                                _ => {
                                    let e = param_exprs[arg.ident().as_str()].clone();
                                    args.push(e);
                                }
                            }
                        } else if arg.ident().as_str() == "sz" {
                            args.push(C::Expr::new_num(page_size as u64))
                        } else {
                            let e = param_exprs[arg.ident().as_str()].clone();
                            args.push(e);
                        }
                    }

                    while_block
                        .body()
                        .fn_call(&unit.to_op_fn_name_on_unit(op, dest_unit), args);
                    while_block.body().assign(
                        sz.clone(),
                        C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
                    );
                    while_block.body().assign(
                        va.clone(),
                        C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
                    );
                    while_block.body().assign(
                        pa.clone(),
                        C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
                    );

                    if_block.then_branch().while_loop(while_block);
                    body.ifelse(if_block);

                    body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

                    scope.push_function(fun);
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_higher_order_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    op_name: &str,
) {
    let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(_) => {
            let op = unit.get_method(op_name).unwrap();

            let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
            fun.set_static().set_inline();

            let mut param_exprs = HashMap::new();

            let v = fun
                .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                .to_expr();
            param_exprs.insert("unit", v.clone());
            for f in op.params.iter() {
                let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
                param_exprs.insert(f.ident().as_str(), p.to_expr());
            }

            let va = &param_exprs["va"];
            let sz = &param_exprs["sz"];
            let body = &mut fun.body();

            // add assertions
            for arg in [va, sz] {
                body.fn_call(
                    "assert",
                    vec![C::Expr::binop(
                        C::Expr::binop(arg.clone(), "%", C::Expr::new_num(base_page_size as u64)),
                        "==",
                        C::Expr::new_num(0),
                    )],
                );
            }

            let original_sz = body
                .new_variable("original_sz", C::Type::new_size())
                .to_expr();
            body.assign(original_sz.clone(), sz.clone());

            let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                sz.clone(),
                ">=",
                C::Expr::new_num(base_page_size as u64),
            ));
            let changed = while_block
                .body()
                .new_variable("changed", C::Type::new_size())
                .to_expr();

            let mut args = vec![C::Expr::addr_of(&v)];
            args.extend(
                op.params
                    .iter()
                    .map(|param| param_exprs[param.ident().as_str()].clone()),
            );
            while_block.body().assign(
                changed.clone(),
                C::Expr::fn_call(&unit.to_op_fn_name_one(op), args),
            );
            while_block
                .body()
                .assign(sz.clone(), C::Expr::binop(sz.clone(), "-", changed.clone()));
            while_block
                .body()
                .assign(va.clone(), C::Expr::binop(va.clone(), "+", changed));

            body.while_loop(while_block);
            body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

            scope.push_function(fun);
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_higher_order_functions(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
) {
    add_higher_order_map(scope, ast, unit, relations);
    add_higher_order_function(scope, unit, relations, "unmap");
    add_higher_order_function(scope, unit, relations, "protect");
}

fn add_op_fn_body_listcomp(
    scope: &mut C::Block,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
    variant_unit: Option<&VelosiAstUnit>,
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
    let fn_name = match variant_unit {
        Some(variant_unit) => dest_unit.to_op_fn_name_on_unit(op, variant_unit),
        None => dest_unit.to_op_fn_name(op),
    };

    scope.return_expr(C::Expr::fn_call(&fn_name, args));
}

fn add_op_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    op_name: &str,
) {
    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: explicit map
        }
        VelosiAstStaticMap::ListComp(map) => {
            let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
            match dest_unit {
                VelosiAstUnit::Enum(e) if op_name == "map" => {
                    for variant in e.get_next_unit_idents() {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let op = variant_unit.get_method(op_name).unwrap();

                        // declare the function
                        let mut fun = C::Function::with_string(
                            unit.to_op_fn_name_on_unit(op, variant_unit),
                            C::Type::new_size(),
                        );
                        fun.set_static().set_inline();

                        let mut param_exprs = HashMap::new();

                        let v = fun
                            .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                            .to_expr();
                        param_exprs.insert("unit", v);
                        for f in op.params.iter() {
                            let p =
                                fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
                            param_exprs.insert(f.ident().as_str(), p.to_expr());
                        }

                        // todo: add requires

                        add_op_fn_body_listcomp(
                            fun.body(),
                            ast,
                            unit,
                            map,
                            op,
                            Some(variant_unit),
                            param_exprs,
                        );

                        // push the function to the scope
                        scope.push_function(fun);
                    }
                }
                _ => {
                    let op = if dest_unit.is_enum() {
                        unit.get_method(op_name).unwrap()
                    } else {
                        dest_unit.get_method(op_name).unwrap()
                    };
                    let fn_name = if op_name == "map" {
                        unit.to_op_fn_name_on_unit(op, dest_unit)
                    } else {
                        unit.to_op_fn_name_one(op)
                    };

                    // declare the function
                    let mut fun = C::Function::with_string(fn_name, C::Type::new_size());
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

                    add_op_fn_body_listcomp(fun.body(), ast, unit, map, op, None, param_exprs);

                    // push the function to the scope
                    scope.push_function(fun);
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // no map defined
        }
    }
}

fn add_op_functions(scope: &mut C::Scope, ast: &VelosiAst, unit: &VelosiAstUnitStaticMap) {
    add_op_function(scope, ast, unit, "map");
    add_op_function(scope, ast, unit, "unmap");
    add_op_function(scope, ast, unit, "protect");
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
    relations: &Relations,
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
    for u in unit.map.get_next_unit_idents().iter() {
        let path = format!("../{}/unit.h", u.to_ascii_lowercase());
        s.new_include(&path, false);
    }

    // add the definitions
    add_unit_constants(s, unit);
    add_unit_flags(s, unit);
    generate_unit_struct(s, unit);
    add_constructor_function(s, unit);
    add_higher_order_functions(s, ast, unit, relations);
    add_op_functions(s, ast, unit);

    // add_translate_function(s, unit);

    // save the scope
    log::debug!("saving the scope!");
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;
    Ok(())
}
