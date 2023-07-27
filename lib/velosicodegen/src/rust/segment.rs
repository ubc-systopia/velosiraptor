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

//! Segment Code Generation (Rust)

use std::path::Path;

use codegen_rs as CG;

use velosiast::{
    ast::{VelosiAstMethod, VelosiAstUnitSegment, VelosiOperation},
    VelosiAst, VelosiAstUnit,
};
use velosicomposition::Relations;

use super::utils;
use crate::VelosiCodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut CG::Scope, unit: &VelosiAstUnitSegment) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in unit.consts() {
        utils::add_const_def(scope, c);
    }
}

fn add_segment_struct(
    scope: &mut CG::Scope,
    unit: &VelosiAstUnitSegment,
    ast: &VelosiAst,
    relations: &Relations,
) {
    // create the struct in the scope
    let struct_name = utils::to_struct_name(unit.ident(), None);
    let st = scope.new_struct(&struct_name);

    // make it public
    st.vis("pub");

    st.derive("Copy");
    st.derive("Clone");

    // add the doc field to the struct
    st.doc(&format!(
        "Represents the Unit type '{}'.\n@loc: {}",
        unit.ident(),
        unit.loc.loc()
    ));

    // it has a single field, called 'interface'
    let iface_name = utils::to_struct_name(&struct_name, Some("Interface"));
    st.field("interface", &iface_name);

    // struct impl
    let imp = scope.new_impl(&struct_name);

    // constructor
    let constructor = utils::add_constructor_signature(imp, &struct_name, &unit.params);
    constructor.line(format!(
        "Self {{ interface: {}::new({}) }}",
        iface_name,
        utils::params_to_args_list(&unit.params)
    ));

    // getters
    for p in &unit.params {
        let getter = imp
            .new_fn(p.ident())
            .vis("pub")
            .arg_ref_self()
            .ret(utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
        getter.line(format!("self.interface.{}()", p.ident()));
    }

    // op functions
    let has_children = relations.0.get(unit.ident()).is_some();
    let op = unit.methods.get("map").expect("map method not found!");
    add_op_fn(unit, ast, op, "map", imp);
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_fn(
        unit,
        ast,
        op,
        if has_children { "unmap_table" } else { "unmap" },
        imp,
    );
    let op = unit
        .methods
        .get("protect")
        .expect("protect method not found!");
    add_op_fn(
        unit,
        ast,
        op,
        if has_children {
            "protect_table"
        } else {
            "protect"
        },
        imp,
    );

    // valid function
    add_valid_fn(unit, imp);

    if let Some(children) = relations.0.get(unit.ident()) {
        if !children.is_empty() {
            let child = &children[0];

            // higher-order unmap and protect
            let op = unit.methods.get("unmap").expect("unmap method not found!");
            add_higher_order_fn(op, imp);

            let op = unit
                .methods
                .get("protect")
                .expect("protect method not found!");
            add_higher_order_fn(op, imp);

            // resolve function
            add_resolve_fn(unit, child, imp);
        }
    }
}

fn add_op_fn(
    unit: &VelosiAstUnitSegment,
    ast: &VelosiAst,
    method: &VelosiAstMethod,
    method_name: &str,
    imp: &mut CG::Impl,
) {
    let op_fn = imp
        .new_fn(&method_name)
        .vis("pub")
        .arg_ref_self()
        .ret("usize");

    for f in method.params.iter() {
        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
    }

    // add requires
    if method.requires.is_empty() {
        op_fn.line("// no requires clauses");
    } else {
        op_fn.line("// asserts for the requires clauses");
    }
    for r in method.requires.iter() {
        op_fn.line(format!(
            "assert!({});",
            utils::astexpr_to_rust_expr(r, Some(ast))
        ));
    }
    op_fn.line("");

    if !method.ops.is_empty() {
        op_fn.line("// configuration sequence");
        let mut iter = method.ops.iter().peekable();
        while let Some(op) = iter.next() {
            // if next op is a write action, end the method call chain
            if matches!(iter.peek(), Some(VelosiOperation::WriteAction(_))) {
                op_fn.line(utils::op_to_rust_expr(op, &unit.interface, ast, method) + ";");
            } else {
                op_fn.line(utils::op_to_rust_expr(op, &unit.interface, ast, method));
            }
        }

        let page_size: usize = 1 << unit.inbitwidth;
        op_fn.line(format!("{:#x}", page_size));
    } else {
        op_fn.line("// there is no configuration sequence");
        op_fn.line("0");
    }
}

fn add_higher_order_fn(method: &VelosiAstMethod, imp: &mut CG::Impl) {
    let op_fn = imp
        .new_fn(method.ident())
        .vis("pub")
        .arg_ref_self()
        .ret("usize");
    for f in method.params.iter() {
        op_fn.arg(f.ident(), utils::vrs_type_to_rust_type(&f.ptype.typeinfo));
    }
    op_fn.line(format!(
        "self.resolve().{}({})",
        method.ident(),
        utils::params_to_args_list(&method.params)
    ));
}

fn add_valid_fn(unit: &VelosiAstUnitSegment, imp: &mut CG::Impl) {
    let op = unit.methods.get("valid").expect("valid method not found!");
    let valid = imp.new_fn(op.ident()).vis("pub").arg_ref_self().ret("bool");
    for f in unit.state.fields() {
        valid.line(format!(
            "let {} = self.interface.read_{}();",
            f.ident(),
            f.ident()
        ));
    }
    valid.line(utils::astexpr_to_rust_expr(op.body.as_ref().unwrap(), None));
}

fn add_resolve_fn(unit: &VelosiAstUnitSegment, child: &VelosiAstUnit, imp: &mut CG::Impl) {
    // add the translate function as a helper
    let op = unit
        .methods
        .get("translate")
        .expect("map method not found!");
    let translate = imp
        .new_fn("translate")
        .arg_ref_self()
        .ret(utils::vrs_type_to_rust_type(&op.rtype.typeinfo));
    for p in &op.params {
        translate.arg(p.ident(), utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
    }

    for f in unit.state.fields() {
        translate.line(format!(
            "let {} = self.interface.read_{}();",
            f.ident(),
            f.ident()
        ));
    }
    translate.line(utils::astexpr_to_rust_expr(op.body.as_ref().unwrap(), None));

    // add resolve
    let ret_ty = utils::to_struct_name(child.ident(), None);
    let resolve = imp.new_fn("resolve").vis("pub").arg_ref_self().ret(&ret_ty);

    resolve.line("let paddr = self.translate(0);");
    resolve.line(format!(
        "unsafe {{ {}::new({}) }}",
        ret_ty,
        utils::params_to_self_args_list_with_paddr(child.params_as_slice(), "paddr")
    ));
}

/// generates the VelosiAstUnitSegment definitions
pub fn generate(
    unit: &VelosiAstUnitSegment,
    ast: &VelosiAst,
    relations: &Relations,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating segment unit {}", unit.ident());

    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.ident());
    utils::add_header(&mut scope, &title);

    // import utils
    scope.import("crate::utils", "*");
    scope.import("crate::os", "*");

    // add import for the interface
    let iface_name = utils::to_struct_name(unit.ident(), Some("Interface"));
    scope.import("super", &iface_name);
    if let Some(map) = unit.get_method("map") {
        utils::import_referenced_units(&mut scope, map);
    }

    // add the definitions
    add_unit_constants(&mut scope, unit);
    add_segment_struct(&mut scope, unit, ast, relations);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
