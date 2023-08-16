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

//! Enum Generation (Rust)

use std::{path::Path, rc::Rc};

use codegen_rs as CG;

use velosiast::{ast::VelosiAstExpr, VelosiAst, VelosiAstMethod, VelosiAstUnit, VelosiAstUnitEnum};

use super::utils;
use crate::VelosiCodeGenError;

fn generate_unit_struct(scope: &mut CG::Scope, ast: &VelosiAst, unit: &VelosiAstUnitEnum) {
    let enum_name = utils::to_struct_name(unit.ident(), None);

    // enum definition
    let en = scope.new_struct(&enum_name);
    en.vis("pub");
    en.doc(&format!(
        "Unit Type `{}`\n@loc: {}",
        unit.ident(),
        unit.loc.loc(),
    ));
    en.repr("C");

    for param in &unit.params {
        let doc = format!("Parameter '{}' in unit '{}'", param.ident(), unit.ident());
        let loc = format!("@loc: {}", param.loc.loc());
        let mut field = CG::Field::new(
            param.ident(),
            utils::vrs_type_to_rust_type(&param.ptype.typeinfo),
        );
        field.doc(vec![&doc, &loc]);
        en.push_field(field);
    }

    // enum impl
    let imp = scope.new_impl(&enum_name);

    // constructor
    utils::add_constructor(imp, &enum_name, &unit.params);

    // getters
    for p in &unit.params {
        let getter = imp
            .new_fn(p.ident())
            .vis("pub")
            .arg_ref_self()
            .ret(utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
        getter.line(format!("self.{}", p.ident()));
    }

    // add differentiators
    for (variant, differentiator) in unit.get_unit_differentiators() {
        add_differentiator_function(ast.get_unit(&variant).unwrap(), differentiator, imp);
    }

    // op functions
    for variant in unit.get_next_unit_idents() {
        let variant_unit = ast.get_unit(variant).unwrap();
        add_specific_function(variant_unit, "map", imp);
    }

    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_delegate_function(ast, unit, op, imp);
    let op = unit
        .methods
        .get("protect")
        .expect("protect method not found!");
    add_delegate_function(ast, unit, op, imp);

    add_valid_fn(ast, unit, imp);
}

fn add_differentiator_function(
    variant_unit: &VelosiAstUnit,
    differentiator: &[Rc<VelosiAstExpr>],
    imp: &mut CG::Impl,
) {
    if let VelosiAstUnit::Segment(segment) = variant_unit {
        let differentiator_fn = imp
            .new_fn(&format!("is_{}", variant_unit.ident().to_lowercase()))
            .vis("pub")
            .arg_ref_self()
            .ret(CG::Type::from("bool"));
        for f in segment.state.fields() {
            differentiator_fn.line(format!(
                "let {} = unsafe {{ {}::new({}) }}.read_{}();",
                f.ident(),
                utils::to_struct_name(variant_unit.ident(), Some("Interface")),
                utils::params_to_self_args_list(&segment.params),
                f.ident()
            ));
        }
        differentiator_fn.line(
            differentiator
                .iter()
                .map(|e| utils::astexpr_to_rust_expr(e, None))
                .collect::<Vec<_>>()
                .join(" && "),
        );
    } else {
        panic!("expected segment inside enum");
    }
}

fn add_specific_function(variant_unit: &VelosiAstUnit, op_name: &str, imp: &mut CG::Impl) {
    let op = variant_unit.get_method(op_name).unwrap();
    let op_fn = imp
        .new_fn(&format!(
            "{}_{}",
            op_name,
            variant_unit.ident().to_lowercase()
        ))
        .vis("pub")
        .arg_ref_self()
        .ret("usize");

    for f in op.params.iter() {
        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
    }

    op_fn.line(format!(
        "unsafe {{ {}::new({}) }}.{}({})",
        utils::to_struct_name(variant_unit.ident(), None),
        utils::params_to_self_args_list(variant_unit.params_as_slice()),
        op_name,
        utils::params_to_args_list(&op.params),
    ));
}

fn add_delegate_function(
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
    op: &VelosiAstMethod,
    imp: &mut CG::Impl,
) {
    let op_fn = imp
        .new_fn(op.ident())
        .vis("pub")
        .arg_ref_self()
        .ret("usize");

    for f in op.params.iter() {
        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
    }

    // check variant and delegate accordingly
    let variants = &unit.get_next_unit_idents();
    let (first, rest) = variants.split_first().unwrap();
    let first_unit = ast.get_unit(first).unwrap();

    let mut if_block = CG::Block::new(&format!(
        "if self.is_{}()",
        first_unit.ident().to_lowercase()
    ));
    if_block.line(format!(
        "unsafe {{ {}::new({}) }}.{}({})",
        utils::to_struct_name(first_unit.ident(), None),
        utils::params_to_self_args_list(first_unit.params_as_slice()),
        op.ident(),
        utils::params_to_args_list(&op.params),
    ));
    op_fn.push_block(if_block);

    for variant in rest {
        let variant_unit = ast.get_unit(variant).unwrap();
        let mut else_if_block = CG::Block::new(&format!(
            "else if self.is_{}()",
            variant_unit.ident().to_lowercase()
        ));
        else_if_block.line(format!(
            "unsafe {{ {}::new({}) }}.{}({})",
            utils::to_struct_name(variant_unit.ident(), None),
            utils::params_to_self_args_list(variant_unit.params_as_slice()),
            op.ident(),
            utils::params_to_args_list(&op.params),
        ));
        op_fn.push_block(else_if_block);
    }

    let mut panic = CG::Block::new("else");
    panic.line("panic!(\"cannot perform operation on invalid enum\")");

    op_fn.push_block(panic);
}

fn add_valid_fn(ast: &VelosiAst, unit: &VelosiAstUnitEnum, imp: &mut CG::Impl) {
    let valid = imp.new_fn("valid").vis("pub").arg_ref_self().ret("bool");
    valid.line(
        unit.get_next_unit_idents()
            .iter()
            .map(|variant| {
                let variant_unit = ast.get_unit(variant).unwrap();
                format!(
                    "unsafe {{ {}::new({}) }}.valid()",
                    utils::to_struct_name(variant, None),
                    utils::params_to_self_args_list(variant_unit.params_as_slice()),
                )
            })
            .collect::<Vec<_>>()
            .join(" || "),
    );
}

pub fn generate(
    ast: &VelosiAst,
    unit: &VelosiAstUnitEnum,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating enum unit {}", unit.ident());

    // the code generation scope
    let mut scope = CG::Scope::new();

    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    // import utils
    scope.import("crate::utils", "*");

    scope.new_comment("include references to the used units");
    for u in unit.get_next_unit_idents() {
        // import the struct itself as well as its' interface
        scope.import("crate", &utils::to_struct_name(u, None));
        scope.import(
            &format!("crate::{}", u.to_lowercase(),),
            &utils::to_struct_name(u, Some("Interface")),
        );

        let unit = ast.get_unit(u).unwrap();
        if let Some(map) = unit.get_method("map") {
            utils::import_referenced_units(&mut scope, map);
        }
    }

    // add the definitions
    generate_unit_struct(&mut scope, ast, unit);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
