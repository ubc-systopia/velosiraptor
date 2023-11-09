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

//! Enum Generation (C)

use std::path::Path;

use crustal as C;

use velosiast::ast::{VelosiAstTypeInfo, VelosiAstTypeProperty};
use velosiast::{VelosiAst, VelosiAstMethod, VelosiAstUnit, VelosiAstUnitEnum};

use super::utils::{self, UnitUtils};
use crate::VelosiCodeGenError;
use velosicomposition::Relations;

fn generate_unit_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let s = if env.has_map_protect_unmap() {
        let children = relations.get_children_units(unit.ident());

        let mut children_enum = C::Enum::new(&unit.to_child_kind_name());
        let mut children_union = C::Union::new(&unit.to_child_union_name());

        for child in &children {
            // add the type for the children
            children_enum.new_variant(&child.ident().to_ascii_uppercase());
            children_union.new_field(
                &child.ident().to_ascii_lowercase(),
                C::Type::new_typedef(&child.to_type_name()),
            );
        }

        let mut s = C::Struct::new(&unit.to_struct_name());
        s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
        s.push_doc_str("");
        s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

        s.new_field("kind", children_enum.to_type());
        s.new_field("variants", children_union.to_type().to_ptr());

        scope.push_enum(children_enum);
        scope.push_union(children_union);

        // here we don't do anything fancy
        unimplemented!("TODO: handle me!");
    } else {
        let fields = unit
            .params
            .iter()
            .map(|x| C::Field::with_string(x.ident().to_string(), C::Type::new_uintptr()))
            .collect();

        let mut s = C::Struct::with_fields(&unit.to_struct_name(), fields);

        s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
        s.push_doc_str("");
        s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

        s
    };

    let stype = s.to_type();

    // add the struct definition to the scope
    scope.push_struct(s);

    // add the type def to the scope
    scope.new_typedef(&unit.to_type_name(), stype);
}

fn add_constructor_function(scope: &mut C::Scope, unit: &VelosiAstUnitEnum) {
    let mut fun = C::Function::with_string(unit.constructor_fn_name(), C::Type::new_void());
    fun.set_static().set_inline();

    let mut params = Vec::new();

    let unit_expr = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    for p in &unit.params {
        let param = fun.new_param(p.ident(), C::Type::new_uint64()).to_expr();
        params.push((p.ident(), param));
    }

    let body = fun.body();

    let _unittype = unit.to_ctype();
    for (name, p) in params {
        body.assign(C::Expr::field_access(&unit_expr, name), p);
    }

    scope.push_function(fun);
}

use std::collections::HashMap;
use std::collections::HashSet;

fn is_fn_name(unit: &VelosiAstUnitEnum, variant_unit: &VelosiAstUnit) -> String {
    let mut fn_name = unit.to_struct_name();
    fn_name.push_str("_is_");
    fn_name.push_str(
        &variant_unit
            .ident()
            .replace(unit.ident().as_str(), "")
            .to_ascii_lowercase(),
    );
    fn_name
}

// fn add_do_map_function(
//     scope: &mut C::Scope,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitEnum,
// ) -> Result<(), VelosiCodeGenError> {
//     // forall variants, generate one function. that's basically a pass-through!
//     // map_page() map_ptable()
//     //  -> create state struct
//     //  -> call map()

//     for variant in unit.get_next_unit_idents().into_iter() {
//         // lookup the unit

//         let variant_unit = ast.get_unit(variant).expect("unit not found!");
//         let variant_op = variant_unit
//             .get_method("map")
//             .expect("map method not found!");

//         // here we probably want to generate something else

//         // declare the function

//         let fn_name = unit.to_op_fn_name_on_unit(variant_op, variant_unit);

//         let mut fun = C::Function::with_string(fn_name, C::Type::new_size());
//         fun.set_static().set_inline();

//         // add the parameters
//         let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
//         let v_expr = v.to_expr();

//         for f in variant_op.params.iter() {
//             let _p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, false));
//         }

//         let body = fun.body();

//         // call the constructor function of the other type
//         // create local variable for next state
//         let tunit = body
//             .new_variable("targetunit", variant_unit.to_ctype())
//             .to_expr();
//         // st = variant_unit.constructor_fn_name()
//         let args = variant_unit
//             .params_as_slice()
//             .iter()
//             .map(|p| C::Expr::field_access(&v_expr, p.ident().as_str()))
//             .collect();

//         body.assign(
//             tunit.clone(),
//             C::Expr::fn_call(&variant_unit.constructor_fn_name(), args),
//         );

//         let mut args = vec![C::Expr::addr_of(&tunit)];
//         for f in variant_op.params.iter() {
//             args.push(C::Expr::new_var(
//                 f.ident().as_str(),
//                 variant_unit.ptype_to_ctype(&f.ptype.typeinfo, false),
//             ));
//         }
//         let mapexpr = C::Expr::fn_call(&variant_unit.to_op_fn_name(variant_op), args);
//         body.return_expr(mapexpr);

//         scope.push_function(fun);
//     }

//     Ok(())
// }

// fn add_do_op_function(
//     scope: &mut C::Scope,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitEnum,
//     op: &VelosiAstMethod,
// ) -> Result<(), VelosiCodeGenError> {
//     // forall variants, generate one function. that's basically a pass-through!
//     // map_page() map_ptable()
//     //  -> create state struct
//     //  -> call map()
//     let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
//     fun.set_static().set_inline();

//     let v = fun
//         .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//         .to_expr();

//     let mut call_exprs = Vec::new();
//     for f in op.params.iter() {
//         let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, false));
//         call_exprs.push(p.to_expr());
//     }

//     // adding asserts
//     if op.requires.is_empty() {
//         fun.body().new_comment("no requires clauses");
//     } else {
//         fun.body().new_comment("asserts for the requires clauses");
//     }
//     // for r in op.requires.iter() {
//     //     // add asserts!
//     //     fun.body()
//     //         .fn_call("assert", vec![utils::expr_to_cpp(unit, r)]);
//     // }
//     let mut block = C::Block::new();
//     block.fn_call("assert", vec![C::Expr::bfalse()]);

//     for variant in unit.get_next_unit_idents().into_iter() {
//         let variant_unit = ast.get_unit(variant).expect("unit not found!");
//         // let variant_op = variant_unit
//         //     .get_method("translate")
//         //     .expect("map method not found!");

//         let mut fn_name = unit.to_struct_name();
//         fn_name.push_str("_is_");
//         fn_name.push_str(
//             &variant_unit
//                 .ident()
//                 .replace(unit.ident().as_str(), "")
//                 .to_ascii_lowercase(),
//         );

//         let mut then = C::Block::new();
//         let tunit = then
//             .new_variable("targetunit", variant_unit.to_ctype())
//             .to_expr();

//         // st = variant_unit.constructor_fn_name()
//         let args = variant_unit
//             .params_as_slice()
//             .iter()
//             .map(|p| C::Expr::field_access(&v, p.ident().as_str()))
//             .collect();

//         then.assign(
//             tunit.clone(),
//             C::Expr::fn_call(&variant_unit.constructor_fn_name(), args),
//         );

//         let mut args = Vec::new();
//         args.push(C::Expr::addr_of(&tunit));
//         args.extend(call_exprs.clone());

//         then.fn_call(&variant_unit.to_op_fn_name(op), args);

//         let cond = C::Expr::fn_call(fn_name.as_str(), vec![v.clone()]);
//         let mut ifelse = C::IfElse::new(&cond);
//         ifelse.set_then(then).set_other(block);

//         let mut block_new = C::Block::new();
//         block_new.ifelse(ifelse);
//         block = block_new;
//     }

//     fun.set_body(block);

//     scope.push_function(fun);
//     Ok(())
// }

// fn add_do_unmap_function(
//     scope: &mut C::Scope,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitEnum,
// ) -> Result<(), VelosiCodeGenError> {
//     let op = unit.methods.get("unmap").expect("unmap method not found!");
//     add_do_op_function(scope, ast, unit, op)
// }

// fn add_do_protect_function(
//     scope: &mut C::Scope,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitEnum,
// ) -> Result<(), VelosiCodeGenError> {
//     let op = unit
//         .methods
//         .get("protect")
//         .expect("protect method not found!");
//     add_do_op_function(scope, ast, unit, op)
// }

// fn add_translate_function(
//     _scope: &mut C::Scope,
//     _ast: &VelosiAst,
//     _unit: &VelosiAstUnitEnum,
// ) -> Result<(), VelosiCodeGenError> {
//     Ok(())
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helpers
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_fn_params<'a>(
    fun: &mut C::Function,
    unit: &VelosiAstUnitEnum,
    op: &'a VelosiAstMethod,
    osspec: &VelosiAst,
) -> HashMap<&'a str, C::Expr> {
    let env = osspec.osspec().unwrap();

    let mut param_exprs = HashMap::new();

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("$unit", unit_param.clone());

    for f in op.params.iter() {
        let p = if f.ident().as_str() == "pa" {
            if let Some(ty) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                fun.new_param(f.ident(), C::Type::new_typedef(ty.ident.as_str()))
            } else {
                fun.new_param(
                    f.ident(),
                    unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false),
                )
            }
        } else {
            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, false))
        };

        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    param_exprs
}

fn params_to_fn_arguments(
    op: &VelosiAstMethod,
    unit: C::Expr,
    params: &HashMap<&str, C::Expr>,
) -> Vec<C::Expr> {
    let mut args = vec![unit];
    args.extend(op.params.iter().map(|p| params[p.ident().as_str()].clone()));
    args
}

fn sort_variants(variants: &mut [VelosiAstUnit]) {
    variants.sort_by(|a, b| match (a, b) {
        (VelosiAstUnit::Segment(a), VelosiAstUnit::Segment(b)) => {
            if a.maps_frame() && b.maps_table() {
                std::cmp::Ordering::Less
            } else if a.maps_table() && b.maps_frame() {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        }
        _ => unreachable!(),
    });
}

fn construct_next_unit(
    body: &mut C::Block,
    unit: &VelosiAstUnitEnum,
    v_unit: &C::Expr,
    variant: &VelosiAstUnit,
    varname: &str,
) -> C::Expr {
    // create the variable for the next unit
    let v_next = body.new_variable(varname, variant.to_ctype()).to_expr();

    // initialize the variable
    let mut args = vec![C::Expr::addr_of(&v_next)];
    let enum_variant = &unit.enums[variant.ident()];
    args.extend(
        enum_variant
            .args
            .iter()
            .map(|a| C::Expr::field_access(v_unit, a.as_str())),
    );

    body.fn_call(&variant.constructor_fn_name(), args);
    v_next
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allocate / Free Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_free_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return;
    }
    let env = osspec.osspec().unwrap();

    let ptype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr()
    } else {
        unit.to_ctype()
    };

    let fun = scope.new_function(&unit.to_free_fn_name(), C::Type::new_void());
    let _unit_param = fun.new_param("unit", ptype).to_expr();
}

fn add_allocate_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return;
    }

    let env = osspec.osspec().unwrap();

    let rtype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr()
    } else {
        unit.to_ctype()
    };

    let _fun = scope.new_function(&unit.to_allocate_fn_name(), rtype);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Valid Function
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_valid_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    _osspec: &VelosiAst,
) {
    let mut valid = C::Function::with_string(unit.valid_fn_name(), C::Type::new_bool());
    valid.set_static().set_inline();
    let v = valid
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let vars: Vec<_> = unit
        .enums
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let variant_unit = relations.get_unit(variant.0).unwrap();
            construct_next_unit(valid.body(), unit, &v, variant_unit, &format!("v{i}"))
        })
        .collect();

    let expr = unit
        .get_next_unit_idents()
        .iter()
        .enumerate()
        .map(|(i, variant)| {
            let variant_unit = relations.get_unit(variant).unwrap();
            C::Expr::fn_call(
                &variant_unit.valid_fn_name(),
                vec![C::Expr::addr_of(&vars[i])],
            )
        })
        .reduce(|acc, e| C::Expr::binop(acc, "||", e))
        .unwrap();
    valid.body().return_expr(expr);

    scope.push_function(valid);
}

fn add_is_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    _osspec: &VelosiAst,
) {
    // assumptions here:
    //  - all variants have the same parameters, the same state and interface layout!

    // now,  the generic problem of finding which one of the two it is, is a bit involved:
    // 1) find the state that defines this
    // 2) back project onto the interface to find out how to obtain the state
    // 3) read the interface such that the translation behavior doesn't change
    for variant in unit.get_next_unit_idents().into_iter() {
        // lookup the unit
        let variant_unit = relations.get_unit(variant).expect("unit not found!");

        // declare the function

        let fn_name = is_fn_name(unit, variant_unit);

        let mut fun = C::Function::with_string(fn_name, C::Type::new_bool());
        fun.set_static().set_inline();

        // add the parameters
        let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
        let v_expr = v.to_expr();

        let body = fun.body();

        // call the constructor function of the other type
        // create local variable for next state
        let tunit = construct_next_unit(body, unit, &v_expr, variant_unit, "targetunit");

        // TODO:
        // here we actually need a way to access the relevant part of the state...
        // in theory reading the interface may cause some state transition.

        body.new_comment("Extracting the state values\n");

        let differentiators = unit.get_unit_differentiator(variant_unit.ident());

        // obtain all the state references here.
        let mut state_refs = HashSet::new();
        for e in differentiators {
            e.get_state_references(&mut state_refs);
        }

        let iface = variant_unit.interface().unwrap();

        let mut vars = HashMap::new();
        vars.insert("$unit", C::Expr::addr_of(&tunit));

        let state = variant_unit.state().unwrap();
        for sref in &state_refs {
            // TODO: find the slice here!
            let val = iface
                .read_state_expr(sref, state.get_field_range(sref))
                .unwrap();

            let sref_var_name = format!("{}_val", sref.replace('.', "_"));

            // create a new variable
            let sref_var = body
                .new_variable(sref_var_name.as_str(), C::Type::new_uint64())
                .to_expr();

            // assing the value to the variable
            body.assign(sref_var.clone(), variant_unit.expr_to_cpp(&vars, &val));

            // store the variable for later
            vars.insert(sref.as_str(), sref_var);
        }

        body.new_comment("Evaluate boolean expression on the state\n");

        let res_var = body.new_variable("res", C::Type::new_bool()).to_expr();

        // obtain the differentiators
        for (idx, e) in differentiators.iter().enumerate() {
            if idx == 0 {
                body.assign(res_var.clone(), variant_unit.expr_to_cpp(&vars, e));
            } else {
                let val = C::Expr::binop(res_var.clone(), "&&", variant_unit.expr_to_cpp(&vars, e));
                body.assign(res_var.clone(), val);
            }
        }

        body.return_expr(res_var);

        scope.push_function(fun);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Higher Order Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_map_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let mut variants = relations.get_children_units(unit.ident());
    sort_variants(&mut variants);
    let op = variants.first().unwrap().get_method("map").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration with Parameters
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let param_exprs = add_fn_params(fun, unit, op, osspec);

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let fun_body = fun.body();
    for variant in &relations.get_children_units(unit.ident()) {
        let (maps_frame, maps_table) = if let VelosiAstUnit::Segment(a) = variant {
            (a.maps_frame(), a.maps_table())
        } else {
            unreachable!()
        };
        let mfn = variant.get_method("map").unwrap();

        let var_mappings = if env.has_map_protect_unmap() {
            println!("HANDLE ME!");
            HashMap::new()
        } else {
            HashMap::new()
        };

        let cond = if let Some(r0) = mfn.requires.first() {
            let r0 = unit.expr_to_cpp(&var_mappings, r0);
            mfn.requires.iter().skip(1).fold(r0, |acc, f| {
                C::Expr::land(acc, unit.expr_to_cpp(&var_mappings, f))
            })
        } else {
            todo!("should have at least one precondition");
        };

        let variant_body = fun_body.new_ifelse(&cond).then_branch();

        if maps_frame {
            variant_body.new_comment(&format!("Variant: {} mapping frame", variant.ident()));
            if env.has_map_protect_unmap() {
                unimplemented!();
            } else {
                variant_body
                    .new_comment("TODO: check if there is already a valid mapping in there");
                let v_next = construct_next_unit(
                    variant_body,
                    unit,
                    &param_exprs["$unit"],
                    variant,
                    "entry",
                );
                variant_body.return_expr(C::Expr::fn_call(
                    &variant.to_hl_op_fn_name(op),
                    params_to_fn_arguments(op, C::Expr::addr_of(&v_next), &param_exprs),
                ));
            }
        } else if maps_table {
            variant_body.new_comment(&format!("Variant: {} mapping table", variant.ident()));

            if env.has_map_protect_unmap() {
                unimplemented!();
            } else {
                variant_body
                    .new_comment("TODO: check if there is already a valid mapping in there");
                let v_next = construct_next_unit(
                    variant_body,
                    unit,
                    &param_exprs["$unit"],
                    variant,
                    "entry",
                );
                let _next = relations.get_only_child_unit(variant.ident());
                variant_body.return_expr(C::Expr::fn_call(
                    &variant.to_hl_op_fn_name(op),
                    params_to_fn_arguments(op, C::Expr::addr_of(&v_next), &param_exprs),
                ));
            }
        } else {
            unreachable!()
        }
    }

    fun_body.return_expr(C::Expr::bfalse());
}

fn add_unmap_protect_common(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    op: &VelosiAstMethod,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration with Parameters
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let param_exprs = add_fn_params(fun, unit, op, osspec);

    let fun_body = fun.body();
    if env.has_map_protect_unmap() {
        // -----------------------------------------------------------------------------------------
        // Function Body: Implementation for OS Spec
        // -----------------------------------------------------------------------------------------
        fun_body.new_comment("TODO: HANDLE ME!");
        println!("TODO: implement me!");
        fun_body.return_expr(C::Expr::bfalse());
    } else {
        for variant in &relations.get_children_units(unit.ident()) {
            fun_body.new_comment(&format!("Variant: {}", variant.ident()));

            let body = fun_body
                .new_ifelse(&C::Expr::fn_call(
                    &is_fn_name(unit, variant),
                    vec![param_exprs["$unit"].clone()],
                ))
                .then_branch();

            let v_next = construct_next_unit(body, unit, &param_exprs["$unit"], variant, "next");
            body.return_expr(C::Expr::fn_call(
                &variant.to_hl_op_fn_name(op),
                params_to_fn_arguments(op, C::Expr::addr_of(&v_next), &param_exprs),
            ));
        }
    }

    fun_body.return_expr(C::Expr::bfalse());
}

fn add_unmap_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let variants = relations.get_children_units(unit.ident());
    let op = variants.first().unwrap().get_method("unmap").unwrap();
    add_unmap_protect_common(scope, unit, op, relations, osspec);
}

fn add_protect_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let variants = relations.get_children_units(unit.ident());
    let op = variants.first().unwrap().get_method("protect").unwrap();
    add_unmap_protect_common(scope, unit, op, relations, osspec);
}

fn add_resolve_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let rtype = if let Some(ty) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
        C::Type::new_typedef(ty.ident.as_str()).to_ptr()
    } else {
        unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false)
    };

    //
    let fun = scope.new_function(unit.resolve_fn_name().as_str(), C::Type::new_bool());
    fun.set_static().set_inline();

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let vaddr_param = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();

    let paddr_param = fun.new_param("pa", rtype.to_ptr()).to_expr();

    let fun_body = fun.body();
    if env.has_map_protect_unmap() {
        // -----------------------------------------------------------------------------------------
        // Function Body: Implementation for OS Spec
        // -----------------------------------------------------------------------------------------
        fun_body.new_comment("TODO: HANDLE ME!");
        println!("TODO: implement me!");
        fun_body.return_expr(C::Expr::bfalse());
    } else {
        for variant in &relations.get_children_units(unit.ident()) {
            fun_body.new_comment(&format!("Variant: {}", variant.ident()));

            // create the variable for the next unit
            let var_next = C::Variable::new("next", variant.to_ctype());
            let v_next = var_next.to_expr();

            // initialize the variable
            let mut args = vec![C::Expr::addr_of(&v_next)];
            let enum_variant = &unit.enums[variant.ident()];
            args.extend(
                enum_variant
                    .args
                    .iter()
                    .map(|a| C::Expr::field_access(&unit_param.clone(), a.as_str())),
            );

            fun_body
                .new_ifelse(&C::Expr::fn_call(
                    &is_fn_name(unit, variant),
                    vec![unit_param.clone()],
                ))
                .then_branch()
                .variable(var_next)
                .fn_call(&variant.constructor_fn_name(), args)
                .return_expr(C::Expr::fn_call(
                    &variant.resolve_fn_name(),
                    vec![
                        C::Expr::addr_of(&v_next),
                        vaddr_param.clone(),
                        paddr_param.clone(),
                    ],
                ));
        }
    }

    fun_body.return_expr(C::Expr::bfalse());
}

pub fn generate(
    unit: &VelosiAstUnitEnum,
    relations: &Relations,
    osspec: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating enum unit {}", unit.ident());

    // the code generation scope
    let mut scope = C::Scope::new();

    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Includes
    ////////////////////////////////////////////////////////////////////////////////////////////////

    // add systems include
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_include("types.h", false);
    s.new_include("consts.h", false);

    // adding the OS spec header here
    {
        let env = osspec.osspec().unwrap();
        s.new_include(&format!("{}.h", env.ident().to_lowercase()), true);
    }

    // adding includes for each of the children
    {
        let env = osspec.osspec().unwrap();
        if env.has_map_protect_unmap() {
            let group_roots = relations.get_group_roots();
            let mut children = relations.get_children(unit.ident()).to_vec();
            while let Some(child) = children.pop() {
                if group_roots.contains(&child) {
                    s.new_include(&format!("{}_unit.h", child.to_lowercase()), false);
                } else {
                    children.extend(relations.get_children(&child).iter().cloned());
                }
            }
        } else {
            for child in relations.get_children(unit.ident()) {
                s.new_include(&format!("{}_unit.h", child.to_lowercase()), false);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Unit Constants and Constructor
    ////////////////////////////////////////////////////////////////////////////////////////////////

    s.new_comment(" --------------------------- Constants / Constructor -------------------------");

    generate_unit_struct(s, unit, relations, osspec);
    add_constructor_function(s, unit);

    s.new_comment(" ----------------------------- Address Translation  --------------------------");

    s.new_comment(" ---------------------------- Map / Protect/ Unmap ---------------------------");

    // add_do_map_function(s, unit, relations, osspec);
    // add_do_unmap_function(s, unit, relations, osspec);
    // add_do_protect_function(s, unit, relations, osspec);

    // add_translate_function(s, unit);
    add_valid_fn(s, unit, relations, osspec);
    add_is_function(s, unit, relations, osspec);

    s.new_comment(" ----------------------------- Allocate and free ----------------------------");

    add_allocate_function(s, unit, relations, osspec);
    add_free_function(s, unit, relations, osspec);

    s.new_comment(" --------------------------- Higher Order Functions --------------------------");

    add_map_function(s, unit, relations, osspec);
    add_protect_function(s, unit, relations, osspec);
    add_unmap_function(s, unit, relations, osspec);

    // resolve function
    add_resolve_function(s, unit, relations, osspec);

    // save the scope
    log::debug!("saving the scope!");
    let filename = format!("{}_unit.h", unit.ident().to_ascii_lowercase());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;
    Ok(())
}
