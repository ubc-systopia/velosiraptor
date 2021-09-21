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

//! Unit Generation (Rust)

use std::path::Path;

use codegen_rs as CG;

use super::utils;
use crate::ast::Unit;
use crate::codegen::CodeGenError;

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut CG::Scope, unit: &Unit) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in &unit.consts {
        utils::add_const_def(scope, c);
    }
}

/// adds the struct definition of the unit to the scope
fn add_struct_definition(scope: &mut CG::Scope, unit: &Unit) {
    // a field is a struct
    //
    // field_name  --> struct FieldName {  val: u64 };

    // create the struct in the scope
    let st = scope.new_struct(&unit.name);

    // make it public
    st.vis("pub");

    // add the doc field to the struct
    st.doc(&format!(
        "Represents the Unit type '{}'.\n@loc: {}",
        unit.name,
        unit.location()
    ));

    // it has a single field, called 'val'
    //st.field("val", to_rust_type(field.nbits()));
}

fn add_constructor_function(imp: &mut CG::Impl, unit: &Unit) {
    imp.new_fn("new")
        .vis("pub")
        .doc(&format!("Creates a new `{}` unit", unit.name))
        //.ret(CG::Type::new("Self"))
        .line("// TODO: SYNTHESIZE ME");
}

fn add_translate_function(imp: &mut CG::Impl, unit: &Unit) {
    imp.new_fn("translate")
        .vis("pub")
        .doc(&format!("Creates a new {} unit", unit.name))
        //.ret(CG::Type::new("Self"))
        .line("// TODO: SYNTHESIZE ME");
}

fn add_map_function(imp: &mut CG::Impl, unit: &Unit) {
    imp.new_fn("map")
        .vis("pub")
        .doc(&format!("Creates a new {} unit", unit.name))
        //.ret(CG::Type::new("Self"))
        .line("// TODO: SYNTHESIZE ME");
}

fn add_unmap_function(imp: &mut CG::Impl, unit: &Unit) {
    imp.new_fn("unmap")
        .vis("pub")
        .doc(&format!("Creates a new {} unit", unit.name))
        //.ret(CG::Type::new("Self"))
        .line("// TODO: SYNTHESIZE ME");
}

fn add_protect_function(imp: &mut CG::Impl, unit: &Unit) {
    imp.new_fn("protect")
        .vis("pub")
        .doc(&format!("Creates a new {} unit", unit.name))
        //.ret(CG::Type::new("Self"))
        .line("// TODO: SYNTHESIZE ME");
}

fn add_struct_impl(scope: &mut CG::Scope, unit: &Unit) {
    // new implementation
    let mut imp = scope.new_impl(&unit.name);

    // add the new() function
    add_constructor_function(&mut imp, unit);
    add_map_function(&mut imp, unit);
    add_unmap_function(&mut imp, unit);
    add_protect_function(&mut imp, unit);

    add_translate_function(&mut imp, unit);
}

/// generates the Unit definitions
pub fn generate(unit: &Unit, outdir: &Path) -> Result<(), CodeGenError> {
    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.name);
    utils::add_header(&mut scope, &title);

    // add the definitions
    add_unit_constants(&mut scope, unit);
    add_struct_definition(&mut scope, unit);
    add_struct_impl(&mut scope, unit);

    // save the scope
    utils::save_scope(scope, outdir, "unit")
}
