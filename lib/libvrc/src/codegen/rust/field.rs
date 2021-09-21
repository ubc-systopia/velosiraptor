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

//! Field Generation (Rust)

// std includes
use std::path::Path;

// get the code generator
use codegen_rs as CG;

// library internal includes
use super::utils::{
    add_header, save_scope, to_const_name, to_mask_str, to_rust_type, to_struct_name,
};
use crate::ast::{BitSlice, Field};
use crate::codegen::CodeGenError;

/// returns the string of the field type
pub fn field_type(field: &Field) -> String {
    to_struct_name(&field.name, Some("Field"))
}

/// adding a constant value for the mask : const FIELD_MASK : type = value;
fn add_field_constants(scope: &mut CG::Scope, field: &Field) {
    // construct the constant name
    let maskname = format!("{}_MASK", to_const_name(&field.name));
    // print the mask value
    let maskvalue = format!("0x{:x}", field.mask_value());
    // create and add the constant to the scope
    let mconst = scope.new_const(&maskname, to_rust_type(field.nbits()), &maskvalue);
    // adding the document comment
    mconst.doc(vec!["the mask value for the interface fields"]);
    // make it public
    mconst.vis("pub");
}

fn add_struct_definition(scope: &mut CG::Scope, field: &Field) {
    // a field is a struct
    //
    // field_name  --> struct FieldName {  val: u64 };

    // create the struct in the scope
    let st = scope.new_struct(&field_type(field));

    // make it public
    st.vis("pub");

    // add the doc field to the struct
    st.doc(&format!(
        "Represents the interface field '{}',\ndefined in: {}",
        field.name,
        field.location()
    ));

    // it has a single field, called 'val'
    st.field("val", to_rust_type(field.nbits()));
}

fn add_insert_fn(imp: &mut CG::Impl, fname: &str, fbits: u64, sl: &BitSlice) {
    let fnname = format!("insert_{}", sl.name);
    let ftype = to_rust_type(sl.nbits());
    let valtype = to_rust_type(fbits);
    // set function
    imp.new_fn(&fnname)
        .vis("pub")
        .arg_mut_self()
        .arg("val", CG::Type::new(ftype))
        .doc(&format!("inserts value {}.{} in field", fname, sl.name))
        .line(format!(
            "self.val = (self.val & {}) | (((val as {}) & {}) << {})",
            to_mask_str(!sl.mask_value(), fbits),
            valtype,
            to_mask_str((1 << sl.nbits()) - 1, sl.nbits()),
            sl.start
        ));
}

fn add_extract_fn(imp: &mut CG::Impl, fname: &str, sl: &BitSlice) {
    let fnname = format!("extract_{}", sl.name);
    let ftype = to_rust_type(sl.nbits());

    // get function
    imp.new_fn(&fnname)
        .vis("pub")
        .doc(&format!("extracts value {}.{} from field", fname, sl.name))
        .arg_ref_self()
        .ret(CG::Type::new(ftype))
        .line(format!(
            "((self.val >> {}) & {}) as {}",
            sl.start,
            to_mask_str((1 << sl.nbits()) - 1, sl.nbits()),
            ftype
        ));
}

fn add_struct_impl(scope: &mut CG::Scope, field: &Field) {
    // new implementation
    let imp = scope.new_impl(&field_type(field));

    // add the new() function
    imp.new_fn("new")
        .vis("pub")
        .doc(&format!("creates a new {} field value", field.name))
        .ret(CG::Type::new("Self"))
        .line("Self { val: 0 }");

    // add the get/set functions
    for sl in &field.layout {
        add_insert_fn(imp, &field.name, field.nbits(), sl);
        add_extract_fn(imp, &field.name, sl);
    }
}

/// generates the field value interface
pub fn generate(unit: &str, field: &Field, outdir: &Path) -> Result<(), CodeGenError> {
    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("Field interface for `{}::{}`", unit, &field.name);
    add_header(&mut scope, &title);

    // add the definitions
    add_field_constants(&mut scope, &field);
    add_struct_definition(&mut scope, &field);
    add_struct_impl(&mut scope, &field);

    // save the scope
    save_scope(scope, outdir, &field.name.to_lowercase())
}
