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

use velosiast::{VelosiAst, VelosiAstMethod, VelosiAstUnitEnum};

use super::utils::{self, UnitUtils};
use crate::VelosiCodeGenError;

fn generate_unit_struct(scope: &mut C::Scope, unit: &VelosiAstUnitEnum) {
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

fn add_constructor_function(scope: &mut C::Scope, unit: &VelosiAstUnitEnum) {
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

use std::collections::HashMap;
use std::collections::HashSet;

fn add_is_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
) -> Result<(), VelosiCodeGenError> {
    // assumptions here:
    //  - all variants have the same parameters, the same state and interface layout!

    // now,  the generic problem of finding which one of the two it is, is a bit involved:
    // 1) find the state that defines this
    // 2) back project onto the interface to find out how to obtain the state
    // 3) read the interface such that the translation behavior doesn't change

    let mut preconds_state_bits = HashMap::new();
    for (_i, (variant, _params)) in unit.enums.iter().enumerate() {
        let variant_unit = ast.get_unit(variant.as_str()).expect("unit not found!");
        let variant_op = variant_unit
            .get_method("translate")
            .expect("map method not found!");

        let mut state_refs = HashSet::new();
        for (_j, e) in variant_op.requires.iter().enumerate() {
            e.get_state_references(&mut state_refs);
        }

        let my_precond_state_bits = if let Some(state) = variant_unit.state() {
            state.get_field_slice_refs(&state_refs)
        } else {
            HashMap::new()
        };

        // construct the intersection of all bits
        for (k, v) in my_precond_state_bits.iter() {
            if let Some(v2) = preconds_state_bits.get_mut(k) {
                *v2 &= v;
            } else {
                preconds_state_bits.insert(k.clone(), *v);
            }
        }
    }

    for (variant, _params) in unit.enums.iter() {
        // lookup the unit
        let variant_unit = ast.get_unit(variant.as_str()).expect("unit not found!");
        let variant_op = variant_unit
            .get_method("translate")
            .expect("map method not found!");

        // here we probably want to generate something else

        // declare the function

        let mut fn_name = unit.to_struct_name();
        fn_name.push_str("_is_");
        fn_name.push_str(
            &variant_unit
                .ident()
                .replace(unit.ident().as_str(), "")
                .to_ascii_lowercase(),
        );

        let mut fun = C::Function::with_string(fn_name, C::Type::new_bool());
        fun.set_static().set_inline();

        // add the parameters
        let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
        let v_expr = v.to_expr();

        let body = fun.body();

        // call the constructor function of the other type
        // create local variable for next state
        let tunit = body
            .new_variable("targetunit", variant_unit.to_ctype())
            .to_expr();

        // TODO:
        // here we actually need a way to access the relevant part of the state...
        // in theory reading the interface may cause some state transition.
        let args = variant_unit
            .params_as_slice()
            .iter()
            .map(|p| C::Expr::field_access(&v_expr, p.ident().as_str()))
            .collect();

        body.assign(
            tunit.clone(),
            C::Expr::fn_call(&variant_unit.constructor_fn_name(), args),
        );

        let _res_expr = body.new_variable("res", C::Type::new_bool()).to_expr();

        let res_var = C::Expr::new_var("res", C::Type::new_bool());
        let mut idx = 0;
        for e in variant_op.requires.iter() {
            let state_refs = HashSet::new();
            // let _state_bits = e.get_state_references(&mut state_refs);

            let mut my_precond_state_bits = if let Some(state) = variant_unit.state() {
                state.get_field_slice_refs(&state_refs)
            } else {
                HashMap::new()
            };

            for (k, v) in my_precond_state_bits.iter_mut() {
                let mask = preconds_state_bits.get(k).expect("state bit not found!");
                *v &= *mask;
            }

            let st_access_fields = if let Some(interface) = variant_unit.interface() {
                interface.fields_accessing_state(&state_refs, &my_precond_state_bits)
            } else {
                HashSet::new()
            };

            if st_access_fields.is_empty() {
                continue;
            }

            // this is a part of the state that is present in both.

            let vars = HashMap::new();
            // TODO: need to to a back projection here, and select the right interface
            // more over, do the intersection of all of them
            if idx == 0 {
                body.assign(res_var.clone(), variant_unit.expr_to_cpp(&vars, e));
            } else {
                let val = C::Expr::binop(res_var.clone(), "&&", variant_unit.expr_to_cpp(&vars, e));
                body.assign(res_var.clone(), val);
            }

            idx += 1;
        }

        body.return_expr(res_var);

        scope.push_function(fun);
    }

    Ok(())
}

fn add_map_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
) -> Result<(), VelosiCodeGenError> {
    // forall variants, generate one function. that's basically a pass-through!
    // map_page() map_ptable()
    //  -> create state struct
    //  -> call map()

    for (variant, _params) in unit.enums.iter() {
        // lookup the unit

        let variant_unit = ast.get_unit(variant.as_str()).expect("unit not found!");
        let variant_op = variant_unit
            .get_method("map")
            .expect("map method not found!");

        // here we probably want to generate something else

        // declare the function

        let mut fn_name = unit.to_op_fn_name(variant_op);
        fn_name.push('_');
        fn_name.push_str(
            &variant_unit
                .ident()
                .replace(unit.ident().as_str(), "")
                .to_ascii_lowercase(),
        );

        let mut fun = C::Function::with_string(fn_name, C::Type::new_bool());
        fun.set_static().set_inline();

        // add the parameters
        let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
        let v_expr = v.to_expr();

        for f in variant_op.params.iter() {
            let _p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        }

        let body = fun.body();

        // call the constructor function of the other type
        // create local variable for next state
        let tunit = body
            .new_variable("targetunit", variant_unit.to_ctype())
            .to_expr();
        // st = variant_unit.constructor_fn_name()
        let args = variant_unit
            .params_as_slice()
            .iter()
            .map(|p| C::Expr::field_access(&v_expr, p.ident().as_str()))
            .collect();

        body.assign(
            tunit.clone(),
            C::Expr::fn_call(&variant_unit.constructor_fn_name(), args),
        );

        let mut args = vec![C::Expr::addr_of(&tunit)];
        for f in variant_op.params.iter() {
            args.push(C::Expr::new_var(
                f.ident().as_str(),
                variant_unit.ptype_to_ctype(&f.ptype.typeinfo),
            ));
        }
        let mapexpr = C::Expr::fn_call(&variant_unit.to_op_fn_name(variant_op), args);
        body.return_expr(mapexpr);

        scope.push_function(fun);
    }

    Ok(())
}

fn add_op_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
    op: &VelosiAstMethod,
) -> Result<(), VelosiCodeGenError> {
    // forall variants, generate one function. that's basically a pass-through!
    // map_page() map_ptable()
    //  -> create state struct
    //  -> call map()
    let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_bool());
    fun.set_static().set_inline();

    let v = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let mut call_exprs = Vec::new();
    for f in op.params.iter() {
        let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        call_exprs.push(p.to_expr());
    }

    // adding asserts
    if op.requires.is_empty() {
        fun.body().new_comment("no requires clauses");
    } else {
        fun.body().new_comment("asserts for the requires clauses");
    }
    // for r in op.requires.iter() {
    //     // add asserts!
    //     fun.body()
    //         .fn_call("assert", vec![utils::expr_to_cpp(unit, r)]);
    // }
    let mut block = C::Block::new();
    block.fn_call("assert", vec![C::Expr::bfalse()]);

    for (_i, (variant, _params)) in unit.enums.iter().enumerate() {
        let variant_unit = ast.get_unit(variant.as_str()).expect("unit not found!");
        // let variant_op = variant_unit
        //     .get_method("translate")
        //     .expect("map method not found!");

        let mut fn_name = unit.to_struct_name();
        fn_name.push_str("_is_");
        fn_name.push_str(
            &variant_unit
                .ident()
                .replace(unit.ident().as_str(), "")
                .to_ascii_lowercase(),
        );

        let mut then = C::Block::new();
        let tunit = then
            .new_variable("targetunit", variant_unit.to_ctype())
            .to_expr();

        // st = variant_unit.constructor_fn_name()
        let args = variant_unit
            .params_as_slice()
            .iter()
            .map(|p| C::Expr::field_access(&v, p.ident().as_str()))
            .collect();

        then.assign(
            tunit.clone(),
            C::Expr::fn_call(&variant_unit.constructor_fn_name(), args),
        );

        let mut args = Vec::new();
        args.push(C::Expr::addr_of(&tunit));
        args.extend(call_exprs.clone());

        then.fn_call(&variant_unit.to_op_fn_name(op), args);

        let cond = C::Expr::fn_call(fn_name.as_str(), vec![v.clone()]);
        let mut ifelse = C::IfElse::new(&cond);
        ifelse.set_then(then).set_other(block);

        let mut block_new = C::Block::new();
        block_new.ifelse(ifelse);
        block = block_new;
    }

    fun.set_body(block);

    scope.push_function(fun);
    Ok(())
}

fn add_unmap_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
) -> Result<(), VelosiCodeGenError> {
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_function(scope, ast, unit, op)
}

fn add_protect_function(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
) -> Result<(), VelosiCodeGenError> {
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_function(scope, ast, unit, op)
}

fn add_translate_function(
    _scope: &mut C::Scope,
    _ast: &VelosiAst,
    _unit: &VelosiAstUnitEnum,
) -> Result<(), VelosiCodeGenError> {
    Ok(())
}

pub fn generate(
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
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

    // add systems include
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    generate_unit_struct(s, unit);
    add_constructor_function(s, unit);
    add_is_function(s, ast, unit)?;
    add_map_function(s, ast, unit)?;
    add_unmap_function(s, ast, unit)?;
    add_protect_function(s, ast, unit)?;
    add_translate_function(s, ast, unit)?;

    // save the scope
    log::debug!("saving the scope!");
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;
    Ok(())
}
