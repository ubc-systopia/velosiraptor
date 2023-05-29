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

use velosiast::ast::{VelosiAstMethod, VelosiAstUnitSegment, VelosiOperation};

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

fn add_unit_flags(scope: &mut CG::Scope, unit: &VelosiAstUnitSegment) {
    let structname = utils::to_struct_name(unit.ident(), Some("Flags"));

    if let Some(flags) = &unit.flags {
        scope.new_comment("Defined unit flags");

        let st = scope.new_struct(&structname);
        for flag in &flags.flags {
            st.field(flag.ident(), "bool").vis("pub");
        }
    } else {
        scope.new_comment("Unit has no defined flags");
        scope.new_struct(&structname);
    }
}

fn add_segment_struct(scope: &mut CG::Scope, unit: &VelosiAstUnitSegment) {
    // create the struct in the scope
    let struct_name = utils::to_struct_name(unit.ident(), None);
    let st = scope.new_struct(&struct_name);

    // make it public
    st.vis("pub");

    // add the doc field to the struct
    st.doc(&format!(
        "Represents the Unit type '{}'.\n@loc: {}",
        unit.ident(),
        unit.loc.loc()
    ));

    // it has a single field, called 'interface'
    let iface_name = utils::to_struct_name(&struct_name, Some("Interface"));
    st.field("interface", &format!("&'static {iface_name}"));

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
        .ret(CG::Type::new("Self"))
        .set_unsafe(true)
        .line(format!(
            "Self {{ interface: {}::from_addr(base) }}",
            iface_name
        ));

    // op functions
    let op = unit.methods.get("map").expect("map method not found!");
    add_op_fn(unit, op, imp);
    let op = unit.methods.get("unmap").expect("unmap method not found!");
    add_op_fn(unit, op, imp);
    let op = unit
        .methods
        .get("protect")
        .expect("protect method not found!");
    add_op_fn(unit, op, imp);
}

fn add_op_fn(unit: &VelosiAstUnitSegment, op: &VelosiAstMethod, imp: &mut CG::Impl) {
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

    // add requires
    if op.requires.is_empty() {
        op_fn.line("// no requires clauses");
    } else {
        op_fn.line("// asserts for the requires clauses");
    }
    for r in op.requires.iter() {
        op_fn.line(format!("assert!({});", utils::astexpr_to_rust(r)));
    }
    op_fn.line("");

    if !op.ops.is_empty() {
        op_fn.line("// configuration sequence");
        let mut iter = op.ops.iter().peekable();
        while let Some(op) = iter.next() {
            // if next op is a write action, end the method call chain
            if matches!(iter.peek(), Some(VelosiOperation::WriteAction(_))) {
                op_fn.line(utils::op_to_rust_expr(op) + ";");
            } else {
                op_fn.line(utils::op_to_rust_expr(op));
            }
        }
        op_fn.line("true");
    } else {
        op_fn.line("// there is no configuration sequence");
        op_fn.line("false");
    }
}

/// generates the VelosiAstUnitSegment definitions
pub fn generate(unit: &VelosiAstUnitSegment, outdir: &Path) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating segment unit {}", unit.ident());

    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.ident());
    utils::add_header(&mut scope, &title);

    // add import for the interface
    let iface_name = utils::to_struct_name(&unit.ident(), Some("Interface"));
    scope.import("super", &iface_name);

    // add the definitions
    add_unit_constants(&mut scope, unit);
    add_unit_flags(&mut scope, unit);
    add_segment_struct(&mut scope, unit);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
