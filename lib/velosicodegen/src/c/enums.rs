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

    for variant in unit.get_unit_names().into_iter() {
        // lookup the unit
        let variant_unit = ast.get_unit(variant).expect("unit not found!");

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

        body.new_comment("Extracting the state values\n");

        let differentiators = unit.get_unit_differentiator(variant_unit.ident());

        // obtain all the state references here.
        let mut state_refs = HashSet::new();
        for e in differentiators {
            e.get_state_references(&mut state_refs);
        }

        let iface = variant_unit.interface().unwrap();

        let mut vars = HashMap::new();
        vars.insert("$unit", tunit.clone());

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

    for variant in unit.get_unit_names().into_iter() {
        // lookup the unit

        let variant_unit = ast.get_unit(variant).expect("unit not found!");
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

    for variant in unit.get_unit_names().into_iter() {
        let variant_unit = ast.get_unit(variant).expect("unit not found!");
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
