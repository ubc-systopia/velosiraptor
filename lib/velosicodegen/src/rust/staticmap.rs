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

use std::{path::Path, rc::Rc};

use codegen_rs as CG;

use velosiast::{
    ast::VelosiAstTypeInfo, VelosiAst, VelosiAstMethod, VelosiAstStaticMap,
    VelosiAstStaticMapListComp, VelosiAstUnit, VelosiAstUnitStaticMap,
};
use velosicomposition::Relations;

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

fn add_higher_order_map(
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    imp: &mut CG::Impl,
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
                    let op_fn = imp
                        .new_fn(op.ident())
                        .vis("pub")
                        .arg_mut_self()
                        .ret("usize");
                    for f in op.params.iter() {
                        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
                    }

                    op_fn.line(format!("assert!(va % {:#x} == 0);", base_page_size));
                    op_fn.line(format!("assert!(sz % {:#x} == 0);", base_page_size));
                    op_fn.line(format!("assert!(pa % {:#x} == 0);", base_page_size));
                    op_fn.line("");

                    let (has_children, no_children): (Vec<_>, Vec<_>) = e
                        .get_next_unit_idents()
                        .into_iter()
                        .partition(|variant| relations.0.get(*variant).is_some());

                    // TODO: doesn't handle multiple no_children variants
                    if let Some(variant) = no_children.first() {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let page_size: usize = 1 << variant_unit.input_bitwidth();

                        op_fn.line(format!("self.prepare(sz / {:#x});", page_size));
                        op_fn.line("");
                    }

                    op_fn.line("let mut va = va;");
                    op_fn.line("let mut sz = sz;");
                    op_fn.line("let mut pa = pa;");
                    op_fn.line("let original_sz = sz;");
                    op_fn.line("");

                    for variant in no_children {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let page_size: usize = 1 << variant_unit.input_bitwidth();

                        let mut if_block = CG::Block::new(&format!(
                            "if va % {:#x} == 0 && pa % {:#x} == 0 && sz >= {:#x}",
                            page_size, page_size, page_size,
                        ));
                        if_block.line(format!(
                            "let i = va >> {:#x};",
                            variant_unit.input_bitwidth()
                        ));

                        let mut while_block = CG::Block::new(&format!(
                            "while va >> {:#x} == i && sz >= {:#x}",
                            variant_unit.input_bitwidth(),
                            page_size
                        ));
                        while_block.line(format!(
                            "self.map_{}(va, {:#x}, flgs, pa);",
                            variant_unit.ident().to_lowercase(),
                            page_size,
                        ));
                        while_block.line(format!("sz -= {:#x};", page_size));
                        while_block.line(format!("va += {:#x};", page_size));
                        while_block.line(format!("pa += {:#x};", page_size));

                        if_block.push_block(while_block);
                        op_fn.push_block(if_block);

                        op_fn.line("");
                    }

                    for variant in &has_children {
                        let children = relations.0.get(*variant).unwrap();
                        let child = &children[0];
                        let variant_unit = ast.get_unit(variant).unwrap();

                        for p in &unit.params {
                            op_fn.line(format!("let {} = &self.{};", p.ident(), p.ident()));
                        }
                        op_fn.line(format!(
                            "let i = va >> {:#x};",
                            variant_unit.input_bitwidth()
                        ));
                        op_fn.line(format!(
                            "let entry = unsafe {{ {}::new({}) }};",
                            utils::to_struct_name(dest_unit.ident(), None),
                            map.elm
                                .dst
                                .args
                                .iter()
                                .map(|e| utils::astexpr_to_rust_expr(e, None))
                                .collect::<Vec<_>>()
                                .join(", "),
                        ));

                        let mut if_block = CG::Block::new("if !entry.valid()");
                        if_block.line(format!(
                            "let pa = {}::alloc();",
                            utils::to_struct_name(child.ident(), None),
                        ));
                        if_block.line(format!(
                            "self.map_{}({});",
                            variant_unit.ident().to_lowercase(),
                            utils::params_to_args_list(&op.params),
                        ));

                        op_fn.push_block(if_block);
                        op_fn.line("");

                        op_fn.line(format!(
                            "let mut entry = unsafe {{ {}::new({}) }};",
                            utils::to_struct_name(variant_unit.ident(), None),
                            utils::params_to_self_args_list_with_paddr(
                                dest_unit.params_as_slice(),
                                "entry.base()"
                            ),
                        ));
                        op_fn.line("let child = entry.resolve();");
                        op_fn.line(format!(
                            "let mapped_sz = child.map({});",
                            utils::params_to_args_list(&op.params)
                        ));
                        op_fn.line("sz -= mapped_sz;");
                        if variant != has_children.last().unwrap() {
                            op_fn.line("va += mapped_sz as u64;");
                            op_fn.line("pa += mapped_sz as u64;");
                        }
                        op_fn.line("");
                    }

                    op_fn.line("original_sz - sz");
                }
                _ => {
                    let op = unit.get_method("map").unwrap();
                    let op_fn = imp
                        .new_fn(op.ident())
                        .vis("pub")
                        .arg_mut_self()
                        .ret("usize");
                    for f in op.params.iter() {
                        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
                    }

                    op_fn.line(format!("assert!(va % {:#x} == 0);", base_page_size));
                    op_fn.line(format!("assert!(sz % {:#x} == 0);", base_page_size));
                    op_fn.line(format!("assert!(pa % {:#x} == 0);", base_page_size));
                    op_fn.line("");

                    op_fn.line(format!("self.prepare(sz / {:#x});", base_page_size));
                    op_fn.line("");

                    op_fn.line("let mut va = va;");
                    op_fn.line("let mut sz = sz;");
                    op_fn.line("let mut pa = pa;");
                    op_fn.line("let original_sz = sz;");
                    op_fn.line("");

                    let page_size: usize = 1 << dest_unit.input_bitwidth();
                    let mut if_block = CG::Block::new(&format!(
                        "if va % {:#x} == 0 && pa % {:#x} == 0 && sz >= {:#x}",
                        page_size, page_size, page_size,
                    ));
                    if_block.line(format!("let i = va >> {:#x};", dest_unit.input_bitwidth()));
                    let mut while_block = CG::Block::new(&format!(
                        "while va >> {:#x} == i && sz >= {:#x}",
                        dest_unit.input_bitwidth(),
                        page_size
                    ));

                    let op = if dest_unit.is_enum() {
                        unit.get_method("map").unwrap()
                    } else {
                        dest_unit.get_method("map").unwrap()
                    };
                    while_block.line(format!(
                        "self.map_{}(va, {:#x}, flgs, {});",
                        dest_unit.ident().to_lowercase(),
                        page_size,
                        match &op.params_map["pa"].ptype.typeinfo {
                            VelosiAstTypeInfo::TypeRef(ty) => {
                                let child = ast.get_unit(ty).unwrap();
                                format!(
                                    "unsafe {{ {}::new({}) }}",
                                    utils::to_struct_name(ty, None),
                                    utils::params_to_self_args_list_with_paddr(
                                        child.params_as_slice(),
                                        "pa"
                                    )
                                )
                            }
                            _ => "pa".to_string(),
                        }
                    ));
                    while_block.line(format!("sz -= {:#x};", page_size));
                    while_block.line(format!("va += {:#x};", page_size));
                    while_block.line(format!("pa += {:#x};", page_size));

                    if_block.push_block(while_block);
                    op_fn.push_block(if_block);
                    op_fn.line("");

                    op_fn.line("original_sz - sz");
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_higher_order_fn(
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    op_name: &str,
    imp: &mut CG::Impl,
) {
    let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(_) => {
            let op = unit.get_method(op_name).unwrap();
            let op_fn = imp
                .new_fn(op.ident())
                .vis("pub")
                .arg_mut_self()
                .ret("usize");
            for f in op.params.iter() {
                op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
            }

            op_fn.line(format!("assert!(va % {:#x} == 0);", base_page_size));
            op_fn.line(format!("assert!(sz % {:#x} == 0);", base_page_size));
            op_fn.line("");

            op_fn.line("let mut va = va;");
            op_fn.line("let mut sz = sz;");
            op_fn.line("let original_sz = sz;");
            op_fn.line("");

            let mut while_block = CG::Block::new(&format!("while sz >= {:#x}", base_page_size));
            while_block.line(format!(
                "let changed = self.{}_one({});",
                op_name,
                utils::params_to_args_list(&op.params)
            ));
            while_block.line("sz -= changed;");
            while_block.line("va += changed as u64;");
            op_fn.push_block(while_block);
            op_fn.line("");

            op_fn.line("original_sz - sz");
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

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

fn add_op_fn_body_listcomp(
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    op_fn: &mut CG::Function,
    dest_unit: &VelosiAstUnit,
    op: &VelosiAstMethod,
    suffix: Option<&str>,
) {
    // idx = va / element_size
    op_fn.line(format!(
        "let {} = va >> {:#x};",
        map.var.ident(),
        dest_unit.input_bitwidth()
    ));

    // va = va & (element_size - 1)
    op_fn.line(format!(
        "let va = va & ((0x1 << {:#x}) - 0x1);",
        dest_unit.input_bitwidth()
    ));

    // target_unit = Unit(args..);
    match op.ident().as_str() {
        "map" => {
            // set up fields
            for p in &unit.params {
                op_fn.line(format!("let {} = &self.{};", p.ident(), p.ident()));
            }

            op_fn.line(format!(
                "let mut target_unit = unsafe {{ {}::new({}) }};",
                utils::to_struct_name(dest_unit.ident(), None),
                map.elm
                    .dst
                    .args
                    .iter()
                    .map(|e| utils::astexpr_to_rust_expr(e, None))
                    .collect::<Vec<_>>()
                    .join(", "),
            ));
        }
        "unmap" => {
            if map.is_repr_list() {
                op_fn.line("let child_idx = self.children.iter().position(|(idx, _)| idx == &(i as usize)).unwrap();");
                op_fn.line("let mut target_unit = self.children.remove(child_idx).1;");
            } else {
                op_fn.line("let mut target_unit = self.children[i as usize].take().unwrap();");
            }
        }
        "protect" => {
            if map.is_repr_list() {
                op_fn.line("let target_unit = self.children.iter_mut().find(|(idx, _)| idx == &(i as usize)).map(|(_, entry)| entry).unwrap();");
            } else {
                op_fn.line("let target_unit = self.children[i as usize].as_mut().unwrap();");
            }
        }
        _ => unreachable!(),
    }

    // target_unit.op(args)
    let op_name = match suffix {
        Some(suffix) => format!("{}_{}", op.ident(), suffix),
        None => op.ident_to_string(),
    };

    op_fn.line(format!(
        "let result = target_unit.{}({});",
        op_name,
        utils::params_to_args_list(&op.params)
    ));

    if op.ident().as_str() == "map" {
        if map.is_repr_list() {
            op_fn.line("self.children.push((i as usize, target_unit));");
        } else {
            op_fn.line("self.children[i as usize] = Some(target_unit);");
        }
    }
    op_fn.line("result");
}

fn add_op_function(
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    op_name: &str,
    imp: &mut CG::Impl,
) {
    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(map) => {
            let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
            match dest_unit {
                VelosiAstUnit::Enum(e) if op_name == "map" => {
                    for variant in e.get_next_unit_idents() {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let op = variant_unit.get_method(op_name).unwrap();
                        let op_fn = imp
                            .new_fn(&format!(
                                "{}_{}",
                                op.ident(),
                                variant_unit.ident().to_lowercase()
                            ))
                            .vis("pub")
                            .arg_mut_self()
                            .ret("usize");

                        for f in op.params.iter() {
                            op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
                        }
                        op_fn.line(format!("// {}", map));
                        add_op_fn_body_listcomp(
                            unit,
                            map,
                            op_fn,
                            dest_unit,
                            op,
                            Some(&variant_unit.ident().to_lowercase()),
                        );
                    }
                }
                _ => {
                    let op = if dest_unit.is_enum() {
                        unit.get_method(op_name).unwrap()
                    } else {
                        dest_unit.get_method(op_name).unwrap()
                    };
                    let fn_name = if op_name == "map" {
                        format!("map_{}", dest_unit.ident().to_lowercase())
                    } else {
                        format!("{}_one", op.ident())
                    };
                    let op_fn = imp.new_fn(&fn_name).vis("pub").arg_mut_self().ret("usize");

                    for f in op.params.iter() {
                        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
                    }

                    op_fn.line(format!("// {}", map));
                    add_op_fn_body_listcomp(unit, map, op_fn, dest_unit, op, None);
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_alloc_fn(imp: &mut CG::Impl, struct_name: String) {
    let alloc_fn = imp
        .new_fn("alloc")
        .vis("pub")
        .doc(&format!(
            "Allocates a new {} in a possibly OS dependent way.",
            struct_name
        ))
        .ret("Self");
    alloc_fn.line("unimplemented!()");
}

fn add_prepare_fn(imp: &mut CG::Impl) {
    let alloc_fn = imp
        .new_fn("prepare")
        .doc("Preparation for mapping in a possibly OS dependent way.")
        .arg_ref_self()
        .arg("num_mappings", "usize");
    alloc_fn.line("unimplemented!()");
}

fn generate_unit_struct(
    scope: &mut CG::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
) {
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
        let mut f = CG::Field::new(
            param.ident(),
            utils::vrs_type_to_rust_type(&param.ptype.typeinfo),
        );
        f.doc(vec![&doc, &loc]);
        st.push_field(f);
    }
    if let VelosiAstStaticMap::ListComp(map) = &unit.map {
        let doc = "Track the children of this unit for shadow page table walk";
        let ty = if map.is_repr_list() {
            format!(
                "Vec<(usize, {})>",
                utils::to_struct_name(map.elm.dst.ident().as_str(), None),
            )
        } else {
            format!(
                "[Option<{}>; {}]",
                utils::to_struct_name(map.elm.dst.ident().as_str(), None),
                map.range.end,
            )
        };
        let mut f = CG::Field::new("children", ty);
        f.doc(vec![doc]);
        st.push_field(f);
    }

    // struct impl
    let imp = scope.new_impl(&struct_name);

    // constructor
    if let VelosiAstStaticMap::ListComp(map) = &unit.map {
        let constructor = utils::add_constructor_signature(imp, &struct_name, &unit.params);
        if map.is_repr_list() {
            constructor.line(format!(
                "Self {{ {}, children: Vec::new() }}",
                utils::params_to_args_list(&unit.params),
            ));
        } else {
            constructor.line(format!(
                "const INIT: Option<{}> = None;",
                utils::to_struct_name(map.elm.dst.ident(), None)
            ));
            constructor.line(format!(
                "Self {{ {}, children: [INIT; {}] }}",
                utils::params_to_args_list(&unit.params),
                map.range.end
            ));
        }
    }
    add_alloc_fn(imp, struct_name);

    // getters
    for p in &unit.params {
        let getter = imp
            .new_fn(p.ident())
            .vis("pub")
            .arg_ref_self()
            .ret(utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
        getter.line(format!("self.{}", p.ident()));
    }

    // add higher-level functions
    add_prepare_fn(imp);
    add_higher_order_map(ast, unit, relations, imp);
    add_higher_order_fn(unit, relations, "unmap", imp);
    add_higher_order_fn(unit, relations, "protect", imp);

    // op functions
    add_op_function(ast, unit, "map", imp);
    add_op_function(ast, unit, "unmap", imp);
    add_op_function(ast, unit, "protect", imp);
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
    let mut scope = CG::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    // import utils
    scope.import("crate::utils", "*");
    scope.import("crate::os", "*");

    // find all the used other units in the static map
    scope.new_comment("include references to the used units");
    for u in unit.map.get_next_unit_idents().iter() {
        scope.import("crate", &utils::to_struct_name(u, None));

        let unit = ast.get_unit(u).unwrap();
        if let Some(map) = unit.get_method("map") {
            utils::import_referenced_units(&mut scope, map);
        }
    }

    if let VelosiAstStaticMap::ListComp(map) = &unit.map {
        if map.is_repr_list() {
            scope.raw("extern crate alloc;");
            scope.import("alloc::vec", "Vec");
        }

        let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
        if let VelosiAstUnit::Enum(e) = dest_unit {
            for variant in e.get_next_unit_idents() {
                if relations.0.get(variant).is_some() {
                    scope.import("crate", &utils::to_struct_name(variant, None));
                }

                let variant_unit = ast.get_unit(variant).unwrap();
                if let Some(map) = variant_unit.get_method("map") {
                    utils::import_referenced_units(&mut scope, map);
                }
            }
        }
    }

    // add the definitions
    add_unit_constants(&mut scope, unit);
    generate_unit_struct(&mut scope, ast, unit, relations);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
