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

//! StaticMap Generation (Rust)

use std::path::Path;

use codegen_rs as CG;

use velosiast::{
    VelosiAst, VelosiAstMethod, VelosiAstStaticMap, VelosiAstStaticMapListComp,
    VelosiAstUnitStaticMap,
};

use super::utils;
use crate::VelosiCodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut CG::Scope, unit: &VelosiAstUnitStaticMap) {
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

fn add_unit_flags(_scope: &mut CG::Scope, _unit: &VelosiAstUnitStaticMap) {
    // TODO: add the flags as a union of all other units this one maps to?
}

fn add_op_fn_body_listcomp(
    op_fn: &mut CG::Function,
    ast: &VelosiAst,
    map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
) {
    op_fn.line(format!("// {}", map.to_string().as_str()));

    // idx = va / element_size
    let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
    op_fn.line(format!(
        "let idx = (va >> {:#x});",
        dest_unit.input_bitwidth()
    ));

    // va = va & (element_size - 1)
    op_fn.line(format!(
        "let va = (va & ((0x1 << {:#x}) - 0x1));",
        dest_unit.input_bitwidth()
    ));

    // target_unit = from_addr((idx * 8) + self.base);
    // TODO: if enum, need to decide which variant to make?
    op_fn.line(format!(
        "let target_unit = unsafe {{ {}::from_addr((idx * 0x8) + self.base) }};",
        utils::to_struct_name(dest_unit.ident(), None)
    ));

    // target_unit.op(va, sz, flgs, pa)
    op_fn.line(format!("target_unit.{}(va, sz, flgs, pa)", op.ident()));
}

fn add_op_function(
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    op: &VelosiAstMethod,
    imp: &mut CG::Impl,
) {
    let op_fn = imp
        .new_fn(op.ident())
        .vis("pub")
        .arg_mut_self()
        .ret(CG::Type::from("bool"));

    for f in op.params.iter() {
        op_fn.arg(
            f.ident(),
            utils::ptype_to_rust_type(&f.ptype.typeinfo, unit.ident()),
        );
    }

    // TODO: add requires

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            op_fn.line("// TODO: Explicit map");
        }
        VelosiAstStaticMap::ListComp(map) => {
            add_op_fn_body_listcomp(op_fn, ast, map, op);
        }
        VelosiAstStaticMap::None(_) => {
            op_fn.line("// No map defined for this unit");
        }
    }
}

fn generate_unit_struct(scope: &mut CG::Scope, ast: &VelosiAst, unit: &VelosiAstUnitStaticMap) {
    let struct_name = utils::to_struct_name(unit.ident(), None);

    // struct definition
    let st = scope.new_struct(&struct_name);
    st.vis("pub");
    st.doc(&format!(
        "Unit Type `{}`\n@loc: {}",
        unit.ident(),
        unit.loc.loc(),
    ));
    st.repr("C");

    for param in &unit.params {
        let doc = format!("Parameter '{}' in unit '{}'", param.ident(), unit.ident());
        let loc = format!("@loc: {}", param.loc.loc());
        let mut f = CG::Field::new(param.ident(), "u64"); // TODO: what type, uintptr in c
        f.doc(vec![&doc, &loc]);
        st.push_field(f);
    }

    // struct impl
    let imp = scope.new_impl(&struct_name);

    // constructor
    imp.new_fn("from_addr")
        .vis("pub")
        .arg("base", "u64")
        .doc(&format!(
            "creates a new reference to a {} unit",
            unit.ident()
        ))
        .ret(CG::Type::new("Self")) // TODO: is this the right type? update doc too
        .set_unsafe(true)
        .line("Self { base }");

    // op functions
    let op = unit.methods.get("map").expect("map method not found!");
    add_op_function(ast, unit, op, imp);
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_function(ast, unit, op, imp);
    let op = unit
        .methods
        .get("protect")
        .expect("protect method not found!");
    add_op_function(ast, unit, op, imp);
}

/// generates the staticmap definitions
pub fn generate(
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating staticmap unit {}", unit.ident());

    // the code generation scope
    let mut scope = CG::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    // TODO: add system imports

    // find all the used other units in the static map
    scope.new_comment("include references to the used units");
    for u in unit.map.get_unit_names().iter() {
        let path = format!("{}", u.to_lowercase());
        scope.import(&path, "*");
    }

    // add the definitions
    add_unit_constants(&mut scope, unit);
    add_unit_flags(&mut scope, unit);
    generate_unit_struct(&mut scope, ast, unit);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
