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
    add_header, num_to_rust_type, save_scope, to_const_name, to_mask_str, to_struct_name,
};
use crate::VelosiCodeGenError;
use velosiast::{VelosiAstField, VelosiAstFieldSlice, VelosiAstInterfaceField};

/// returns the string of the field type
pub fn field_type(field: &VelosiAstInterfaceField) -> String {
    to_struct_name(field.ident(), Some("Field"))
}

/// adding a constant value for the mask : const FIELD_MASK : type = value;
fn add_field_constants(scope: &mut CG::Scope, field: &VelosiAstInterfaceField) {
    // construct the constant name
    let maskname = format!("{}_MASK", to_const_name(field.ident()));
    // print the mask value
    let maskvalue = format!("0x{:x}", field.mask());
    // create and add the constant to the scope
    let mconst = scope.new_const(&maskname, num_to_rust_type(field.nbits()), &maskvalue);
    // adding the document comment
    mconst.doc(vec!["the mask value for the interface fields"]);
    // make it public
    mconst.vis("pub");
}

fn add_struct_definition(scope: &mut CG::Scope, field: &VelosiAstInterfaceField) {
    // a field is a struct
    //
    // field_name  --> struct FieldName {  val: u64 };

    // create the struct in the scope
    let st = scope.new_struct(&field_type(field));

    // make it public
    st.vis("pub");

    // add c representation
    st.repr("C");
    st.derive("Copy");
    st.derive("Clone");

    // add the doc field to the struct
    st.doc(&format!(
        "Represents the interface field '{}',\ndefined in: {}",
        field.ident(),
        field.loc().loc()
    ));

    // it has a single field, called 'val'
    st.field("val", num_to_rust_type(field.nbits()));
}

fn add_insert_fn(imp: &mut CG::Impl, fname: &str, fbits: u64, sl: &VelosiAstFieldSlice) {
    let fnname = format!("insert_{}", sl.ident());
    let ftype = num_to_rust_type(sl.nbits());
    let valtype = num_to_rust_type(fbits);
    // set function

    let body = if sl.start != 0 {
        format!(
            "self.val = (self.val & {}) | (((val as {}) & {}) << {});",
            to_mask_str(!sl.mask(), fbits),
            valtype,
            to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits()),
            sl.start
        )
    } else {
        format!(
            "self.val = (self.val & {}) | ((val as {}) & {});",
            to_mask_str(!sl.mask(), fbits),
            valtype,
            to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits())
        )
    };

    imp.new_fn(&fnname)
        .vis("pub")
        .mut_arg_self()
        .arg("val", CG::Type::new(ftype))
        .doc(&format!(
            "inserts value {}.{} in the field",
            fname,
            sl.ident()
        ))
        .ret("Self")
        .line(body)
        .line("self");
}

fn add_extract_fn(imp: &mut CG::Impl, fname: &str, sl: &VelosiAstFieldSlice) {
    let fnname = format!("extract_{}", sl.ident());
    let ftype = num_to_rust_type(sl.nbits());

    let body = if sl.start != 0 {
        format!(
            "((self.val >> {}) & {}) as {}",
            sl.start,
            to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits()),
            ftype
        )
    } else {
        format!(
            "(self.val & {}) as {}",
            to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits()),
            ftype
        )
    };

    // get function
    imp.new_fn(&fnname)
        .vis("pub")
        .doc(&format!(
            "extracts value {}.{} from the field",
            fname,
            sl.ident()
        ))
        .arg_ref_self()
        .ret(CG::Type::new(ftype))
        .line(body);
}

fn add_struct_impl(scope: &mut CG::Scope, field: &VelosiAstInterfaceField) {
    // new implementation
    let imp = scope.new_impl(&field_type(field));

    // add the new() function
    imp.new_fn("new")
        .vis("pub")
        .doc(&format!("creates a new {} field value", field.ident()))
        .arg("val", num_to_rust_type(field.nbits()))
        .ret(CG::Type::new("Self"))
        .line("Self { val }");

    // add the get/set functions
    for sl in field.layout() {
        add_insert_fn(imp, field.ident(), field.nbits(), sl);
        add_extract_fn(imp, field.ident(), sl);
    }
}

fn add_default_impl(scope: &mut CG::Scope, field: &VelosiAstInterfaceField) {
    let imp = scope.new_impl(&field_type(field));
    imp.impl_trait("Default");

    imp.new_fn("default")
        .ret(CG::Type::new("Self"))
        .line("Self::new(0)");
}

/// generates the field value interface
pub fn generate(
    unit: &str,
    field: &VelosiAstInterfaceField,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("Field interface for `{}::{}`", unit, field.ident());
    add_header(&mut scope, &title);

    // add the definitions
    add_field_constants(&mut scope, field);
    add_struct_definition(&mut scope, field);
    add_struct_impl(&mut scope, field);
    add_default_impl(&mut scope, field);

    // save the scope
    save_scope(scope, outdir, &field.ident().to_lowercase())
}
