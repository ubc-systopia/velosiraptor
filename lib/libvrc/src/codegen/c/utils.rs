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

//! C code generation utilities

// get the code generator
use crustal as C;

//
use crate::ast::{AstNodeGeneric, BitSlice, Const, Field, Unit};
use crate::codegen::COPYRIGHT;

/// converts a string slice into a struct string name
/// field_name  --> struct field_name_SUFFIX
pub fn to_struct_name(s: &str, suffix: Option<&str>) -> String {
    let mut s = s.to_string();
    s.push('_');
    if let Some(x) = suffix {
        s.push_str(x);
    }
    s
}

/// converts a string slice into a rusified constant identifier
pub fn to_const_name(s: &str) -> String {
    s.to_uppercase()
}

/// obtains the appropriate rust type for
pub fn to_rust_type(l: u64) -> &'static str {
    match l {
        0..=8 => "uint8_t",
        9..=16 => "uint16_t",
        17..=32 => "uint32_t",
        33..=64 => "uint64_t",
        65..=128 => "uint128_t",
        _ => "unknown",
    }
}

pub fn unit_struct_name(unit: &Unit) -> String {
    unit.name.to_lowercase()
}

pub fn unit_type_name(unit: &Unit) -> String {
    format!("{}_t", unit.name.to_lowercase())
}

/// constructs the struct type name
pub fn field_struct_name(unit: &Unit, field: &Field) -> String {
    format!("{}_{}", unit.name.to_lowercase(), field.name)
}

/// constructs the field type name for a given field.
pub fn field_type_name(unit: &Unit, field: &Field) -> String {
    format!("{}__t", field_struct_name(unit, field))
}

pub fn field_mask_name(unit: &Unit, field: &Field) -> String {
    format!(
        "{}_{}__MASK",
        unit.name.to_uppercase(),
        field.name.to_uppercase()
    )
}

pub fn if_field_wr_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__wr", unit.to_lowercase(), field)
}

pub fn if_field_wr_fn_name(unit: &Unit, field: &Field) -> String {
    if_field_wr_fn_name_str(&unit.name, &field.name)
}

pub fn if_field_rd_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__rd", unit.to_lowercase(), field)
}

pub fn if_field_rd_fn_name(unit: &Unit, field: &Field) -> String {
    if_field_rd_fn_name_str(&unit.name, &field.name)
}

pub fn if_field_wr_slice_fn_name(unit: &Unit, field: &Field, sl: &BitSlice) -> String {
    format!(
        "{}_{}_{}__wr",
        unit.name.to_lowercase(),
        field.name,
        sl.name
    )
}

pub fn if_field_rd_slice_fn_name(unit: &Unit, field: &Field, sl: &BitSlice) -> String {
    format!(
        "{}_{}_{}__rd",
        unit.name.to_lowercase(),
        field.name,
        sl.name
    )
}

pub fn field_slice_extract_fn_name_str(unit: &str, field: &str, sl: &str) -> String {
    format!("{}_{}__extract_{}", unit.to_lowercase(), field, sl)
}

pub fn field_slice_extract_fn_name(unit: &Unit, field: &Field, sl: &BitSlice) -> String {
    field_slice_extract_fn_name_str(&unit.name, &field.name, &sl.name)
}

pub fn field_slice_insert_fn_name_str(unit: &str, field: &str, sl: &str) -> String {
    format!(
        "{}_{}__insert_{}",
        unit.to_lowercase(),
        field.to_lowercase(),
        sl.to_lowercase()
    )
}

pub fn field_slice_insert_fn_name(unit: &Unit, field: &Field, sl: &BitSlice) -> String {
    field_slice_insert_fn_name_str(&unit.name, &field.name, &sl.name)
}

pub fn field_get_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__get_raw", unit.to_lowercase(), field)
}

pub fn field_get_raw_fn_name(unit: &Unit, field: &Field) -> String {
    field_get_raw_fn_name_str(&unit.name, &field.name)
}

pub fn field_set_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__set_raw", unit.to_lowercase(), field.to_lowercase())
}

pub fn field_set_raw_fn_name(unit: &Unit, field: &Field) -> String {
    field_set_raw_fn_name_str(&unit.name, &field.name)
}

pub fn protect_fn_name(unit: &Unit) -> String {
    format!("{}_protect", unit.name.to_lowercase())
}

pub fn unmap_fn_name(unit: &Unit) -> String {
    format!("{}_unmap", unit.name.to_lowercase())
}

pub fn map_fn_name(unit: &Unit) -> String {
    format!("{}_map", unit.name.to_lowercase())
}

pub fn translate_fn_name(unit: &Unit) -> String {
    format!("{}_resolve", unit.name.to_lowercase())
}

pub fn constructor_fn_name(unit: &Unit) -> String {
    format!("{}_init", unit.name.to_lowercase())
}

pub fn mmio_register_read_fn(unit_var: &C::Expr, field: &Field) -> C::Expr {
    if let Some((base, offset)) = &field.stateref {
        let fnname = format!("mmio_register_read_{}", field.length);
        C::Expr::fn_call(
            &fnname,
            vec![
                C::Expr::field_access(unit_var, &base),
                C::Expr::new_num(*offset),
            ],
        )
    } else {
        C::Expr::fn_call("mmio_register_read", vec![])
    }
}

pub fn mmio_register_write_fn(unit_var: &C::Expr, field: &Field, val: &C::Expr) -> C::Expr {
    if let Some((base, offset)) = &field.stateref {
        let fnname = format!("mmio_register_write_{}", field.length);
        C::Expr::fn_call(
            &fnname,
            vec![
                C::Expr::field_access(unit_var, &base),
                C::Expr::new_num(*offset),
                val.clone(),
            ],
        )
    } else {
        C::Expr::fn_call("mmio_register_read", vec![])
    }
}

/// creates a strng reprsenting the mask value
pub fn to_mask_str(m: u64, len: u64) -> String {
    match len {
        0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
        9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
        17..=32 => format!("0x{:08x}U", (m & 0xffffffff) as u32),
        33..=64 => format!("0x{:016x}ULL", m),
        _ => String::from("unknown"),
    }
}

/// adds the header to the file
pub fn add_header(scope: &mut C::Scope, title: &str) {
    // set the title of the file
    // construct the license

    // adding the autogenerated warning
    scope.push_doc_str(COPYRIGHT);
    scope.new_comment("THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER");
}

pub fn add_const_def(scope: &mut C::Scope, c: &Const) {
    let mut m = C::Macro::new(c.name());
    let e = c.value(); //.fold_constants();
    if c.is_integer() {
        m.set_value(&format!("(uint64_t)({})", e));
    } else {
        m.set_value(&format!("{}", e));
    }

    // add some documentation
    m.doc_str(&format!("Defined constant `{}`", c.name()));
    m.doc_str("");
    m.doc_str(&format!("@loc: {}", c.loc().location()));

    scope.push_macro(m);
}
