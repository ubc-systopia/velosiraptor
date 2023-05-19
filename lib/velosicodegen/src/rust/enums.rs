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

use codegen_rs as CG;

use velosiast::{VelosiAstMethod, VelosiAstUnitEnum};

use super::utils;
use crate::VelosiCodeGenError;

fn generate_unit_struct(scope: &mut CG::Scope, unit: &VelosiAstUnitEnum) {
    let enum_name = utils::to_struct_name(unit.ident(), None);

    // enum definition
    let en = scope.new_enum(&enum_name);
    en.vis("pub");
    en.doc(&format!(
        "Unit Type `{}`\n@loc: {}",
        unit.ident(),
        unit.loc.loc(),
    ));
    en.repr("C");

    // TODO: do we need to consider the enum parameters
    for (variant, _) in &unit.enums {
        let doc = format!("Variant '{}' in unit '{}'", variant.ident(), unit.ident());
        let loc = format!("@loc: {}", variant.loc.loc());
        let variant_name = utils::to_struct_name(variant.ident(), None);
        let mut variant = CG::Variant::new(&variant_name);
        variant.tuple(&variant_name);
        variant.doc(&format!("{doc}\n{loc}"));
        en.push_variant(variant);
    }

    // enum impl
    let imp = scope.new_impl(&enum_name);

    // TODO: constructor?

    // op functions
    let op = unit.methods.get("map").expect("map method not found!");
    add_op_function(unit, op, imp);
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_function(unit, op, imp);
    let op = unit
        .methods
        .get("protect")
        .expect("protect method not found!");
    add_op_function(unit, op, imp);
}

fn add_op_function(unit: &VelosiAstUnitEnum, op: &VelosiAstMethod, imp: &mut CG::Impl) {
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

    // check variant and delegate accordingly
    let mut block = CG::Block::new("match self");
    for (variant, _) in &unit.enums {
        block.line(format!(
            "Self::{}(inner) => inner.{}(va, sz, flgs, pa),",
            utils::to_struct_name(variant.ident(), None),
            op.ident(),
        ));
    }
    op_fn.push_block(block);
}

pub fn generate(unit: &VelosiAstUnitEnum, outdir: &Path) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating enum unit {}", unit.ident());

    // the code generation scope
    let mut scope = CG::Scope::new();

    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    // TODO: add system imports

    // add the definitions
    generate_unit_struct(&mut scope, unit);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
