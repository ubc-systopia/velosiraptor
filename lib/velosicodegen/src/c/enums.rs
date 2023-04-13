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

use std::collections::HashMap;
use std::path::Path;

use crustal as C;

use velosiast::{VelosiAst, VelosiAstUnitEnum};

use super::utils::{self,UnitUtils};
use crate::VelosiCodeGenError;

fn generate_unit_struct(scope: &mut C::Scope, unit: &VelosiAstUnitEnum) {
    let fields = unit
        .params
        .iter()
        .map(|x| {
            let n = utils::unit_struct_field_name(x.ident());
            C::Field::with_string(n, C::Type::new_uintptr())
        })
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
    let mut fun = C::Function::with_string(unit.constructor_fn_name(),  unit.to_ctype());
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
        let n = utils::unit_struct_field_name(name);
        body.assign(C::Expr::field_access(&tunit, &n), p);
    }

    body.return_expr(tunit);

    scope.push_function(fun);
}

fn add_map_function(scope: &mut C::Scope, ast: &VelosiAst, unit: &VelosiAstUnitEnum)  -> Result<(), VelosiCodeGenError> {

    // forall variants, generate one function. that's basically a pass-through!
    // map_page() map_ptable()
    //  -> create state struct
    //  -> call map()

    for (variant, params) in unit.enums.iter() {
        // lookup the unit

        let variant_unit = ast.get_unit(variant.as_str()).expect("unit not found!");
        let variant_op = variant_unit.get_method("map").expect("map method not found!");

        // here we probably want to generate something else

        // declare the function

        let mut fn_name = unit.to_op_fn_name(variant_op);
        fn_name.push('_');
        fn_name.push_str(&variant_unit.ident().replace(unit.ident().as_str(), "").to_ascii_lowercase());


        let mut fun = C::Function::with_string(fn_name, C::Type::new_bool());
        fun.set_static().set_inline();

        // add the parameters
        let v = fun.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
        let v_expr = v.to_expr();

        for f in variant_op.params.iter() {
            let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo));
        }

        let body = fun.body();

        // call the constructor function of the other type
        // create local variable for next state
        let tunit = body.new_variable("targetunit", variant_unit.to_ctype()).to_expr();
        // st = variant_unit.constructor_fn_name()
        let mut args = variant_unit.params_as_slice().iter().map(
            |p|
            C::Expr::field_access(&v_expr, p.ident().as_str())
        ).collect();

        body.assign(tunit.clone(), C::Expr::fn_call(
            &variant_unit.constructor_fn_name(),
            args
        ));


        let mut args = vec![C::Expr::addr_of(&tunit)];
        for f in variant_op.params.iter() {
            args.push(C::Expr::new_var(f.ident().as_str(), variant_unit.ptype_to_ctype(&f.ptype.typeinfo)));
        }
        let mapexpr = C::Expr::fn_call(&variant_unit.to_op_fn_name(variant_op), args);
        body.return_expr(mapexpr);

        scope.push_function(fun);
    }



    Ok(())
}

fn add_unmap_function(ast: &VelosiAst, unit: &VelosiAstUnitEnum, outdir: &Path)  -> Result<(), VelosiCodeGenError> {
    Ok(())
}

fn add_protect_function(ast: &VelosiAst, unit: &VelosiAstUnitEnum, outdir: &Path)  -> Result<(), VelosiCodeGenError> {
    Ok(())
}

fn add_translate_function(ast: &VelosiAst, unit: &VelosiAstUnitEnum, outdir: &Path)  -> Result<(), VelosiCodeGenError> {
    Ok(())
}

pub fn generate(ast: &VelosiAst, unit: &VelosiAstUnitEnum, outdir: &Path) -> Result<(), VelosiCodeGenError> {

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
    add_map_function(s, ast, unit)?;

    // add_op_functions(s, ast, unit);
    // add_translate_function(s, unit);

    // save the scope
    log::debug!("saving the scope!");
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;
    Ok(())
}