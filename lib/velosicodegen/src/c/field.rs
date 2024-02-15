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

//! Field Generation (C/CPP)

// std includes
use std::path::Path;

// get the code generator
use crustal as C;

use velosiast::{VelosiAstField, VelosiAst, VelosiAstFieldSlice, VelosiAstInterfaceField, VelosiAstUnit};

// library internal includes
use super::utils::{self, FieldUtils, SliceUtils};
use crate::VelosiCodeGenError;

/// adding a constant value for the mask : const FIELD_MASK : type = value;
fn add_field_constants(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
) {
    // construct the constant name
    let maskname = field.to_mask_name(unit);

    let maskvalue = format!("(uint{}_t)0x{:x}", field.nbits(), field.mask());

    // create and add the constant to the scope
    let mut m = C::Macro::with_name(maskname);
    m.set_value(&maskvalue);

    // add some documentation
    m.doc_str(&format!(
        "Defined constant for masking field `{}`",
        field.ident()
    ));
    m.doc_str("");
    m.doc_str(&format!("@loc: {}", field.loc().loc()));

    // add the macro to the scope
    scope.push_macro(m);
}

/// generates the path of the header file
pub fn if_field_header_path(name: &str) -> String {
    format!("{name}_field.h")
}

fn add_struct_definition(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
) {
    let sn = field.to_struct_name(unit);
    let mut s = C::Struct::with_fields(
        &sn,
        vec![C::Field::new("_val", C::Type::new_uint(field.nbits()))],
    );

    s.push_doc_str(&format!("Field Type `{}`", field.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", field.loc().loc()));

    let stype = s.to_type();
    scope.push_struct(s);

    // adding a type def;
    let fieldtype = field.to_type_name(unit);
    scope.new_typedef(&fieldtype, stype);

    // adding the get value function
    let fnname = field.to_get_val_fn(unit);
    let mut f = C::Function::with_string(fnname, C::Type::new_uint(field.nbits()));
    f.set_static().set_inline();
    f.push_doc_str(&format!("gets value {} in field", field.ident()));
    let p = f.new_param("field", C::Type::new_typedef(&fieldtype));
    let var = C::Expr::from_fn_param(p);
    f.body().return_expr(C::Expr::field_access(&var, "_val"));
    scope.push_function(f);

    // adding the set value function

    let fnname = field.to_set_val_fn(unit);
    let mut f = C::Function::with_string(fnname, C::Type::new_typedef(&fieldtype));
    f.set_static().set_inline();
    f.push_doc_str(&format!("sets value {} in field", field.ident()));
    let v = f.new_param("val", C::Type::new_uint(field.nbits()));
    let rhs = C::Expr::from_fn_param(v);

    let maskname = field.to_mask_name(unit);
    let field_var_decl = C::Variable::new("field", C::Type::new_typedef(&fieldtype));
    let field_var = field_var_decl.to_expr();

    f.body()
        .variable(field_var_decl)
        .assign(
            C::Expr::field_access(&field_var, "_val"),
            C::Expr::binop(
                rhs,
                "&",
                C::Expr::new_var(&maskname, C::Type::new_uint(field.nbits())),
            ),
        )
        .return_expr(field_var);
    scope.push_function(f);
}

/// adds an extraction function
fn add_extract_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
    sl: &VelosiAstFieldSlice,
) {
    let fieldtype = field.to_type_name(unit);

    // adding the get value function
    let fnname = sl.to_extract_fn(unit, field);
    let mut f = C::Function::with_string(fnname, C::Type::new_uint(field.nbits()));
    f.set_static().set_inline();

    f.push_doc_str(&format!(
        "extracts value {}.{} [{}..{}] in field",
        field.ident(),
        sl.ident(),
        sl.start,
        sl.end
    ));
    f.push_doc_str("");
    f.push_doc_str(&format!("@loc: {}", sl.loc.loc()));

    f.new_param("field", C::Type::new_typedef(&fieldtype));

    let body = if sl.start != 0 {
        C::Expr::Raw(format!(
            "((field._val >> {}) & {})",
            sl.start,
            utils::to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits())
        ))
    } else {
        C::Expr::Raw(format!(
            "(field._val & {})",
            utils::to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits()),
        ))
    };

    f.body().return_expr(body);

    scope.push_function(f);
}

/// Generates an insert function taht sets the value of a field value
fn add_insert_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
    sl: &VelosiAstFieldSlice,
) {
    let fieldtype = field.to_type_name(unit);

    let fnname = sl.to_insert_fn(unit, field);
    let mut f = C::Function::with_string(fnname, C::Type::new_typedef(&fieldtype));
    f.set_static().set_inline();

    f.push_doc_str(&format!(
        "inserts value {}.{} [{}..{}] in field",
        field.ident(),
        sl.ident(),
        sl.start,
        sl.end
    ));
    f.push_doc_str("");
    f.push_doc_str(&format!("@loc: {}", sl.loc.loc()));

    let p = f.new_param("field", C::Type::new_typedef(&fieldtype));
    let lhs = C::Expr::from_fn_param(p);
    f.new_param("val", C::Type::new_uint(field.nbits()));

    let body = if sl.start != 0 {
        C::Expr::Raw(format!(
            "(field._val & {}) | ((val & {}) << {})",
            utils::to_mask_str(!sl.mask(), field.nbits()),
            utils::to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits()),
            sl.start
        ))
    } else {
        C::Expr::Raw(format!(
            "(field._val & {}) | (val & {})",
            utils::to_mask_str(!sl.mask(), field.nbits()),
            utils::to_mask_str(((1u128 << sl.nbits()) - 1) as u64, sl.nbits())
        ))
    };
    f.body()
        .assign(C::Expr::field_access(&lhs, "_val"), body)
        .return_expr(C::Expr::new_var("field", C::Type::new_typedef(&fieldtype)));

    scope.push_function(f);
}

/// generates the field value interface
pub fn generate(
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
    outdir: &Path,
    _osspec: &VelosiAst,
) -> Result<(), VelosiCodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // add the header comments
    let title = format!("Field interface for `{}::{}`", unit.ident(), &field.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!(
        "{}_{}_FIELD_H_",
        unit.ident().to_uppercase(),
        field.ident().to_uppercase()
    );
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // includes
    s.new_include("stdint.h", true);

    // add the definitions
    add_field_constants(s, unit, field);
    add_struct_definition(s, unit, field);

    // add the get/set functions
    for sl in field.layout() {
        add_insert_fn(s, unit, field, sl);
        add_extract_fn(s, unit, field, sl);
    }

    // save the scope
    let filename = if_field_header_path(field.ident());
    scope.set_filename(&filename);

    // save the scope
    scope.to_file(outdir, true)?;
    Ok(())
}
