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

//! Rust code generation utilities

// std includes

use std::fs;
use std::path::Path;

// get the code generator
use codegen_rs as CG;

//
use velosiast::ast::{VelosiAstConst, VelosiAstTypeInfo};

use crate::VelosiCodeGenError;
use crate::COPYRIGHT;

/// converts a string slice into a rustified string name
/// field_name  --> struct FieldName
pub fn to_struct_name(s: &str, suffix: Option<&str>) -> String {
    let mut c = s.chars();
    let mut s = match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
    .replace('_', "");

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
        0..=8 => "u8",
        9..=16 => "u16",
        17..=32 => "u32",
        33..=64 => "u64",
        65..=128 => "u128",
        _ => "unknown",
    }
}

/// obtains the appropriate rust type for the type info
pub fn ptype_to_rust_type(ptype: &VelosiAstTypeInfo, unit_ident: &str) -> CG::Type {
    match ptype {
        VelosiAstTypeInfo::Integer => CG::Type::new("u64"),
        VelosiAstTypeInfo::Bool => CG::Type::new("u64"),
        VelosiAstTypeInfo::GenAddr => CG::Type::new("u64"), // TODO: should address types be different?
        VelosiAstTypeInfo::VirtAddr => CG::Type::new("u64"),
        VelosiAstTypeInfo::PhysAddr => CG::Type::new("u64"),
        VelosiAstTypeInfo::Size => CG::Type::new("u64"),
        VelosiAstTypeInfo::Flags => CG::Type::new(&to_struct_name(unit_ident, Some("Flags"))),
        VelosiAstTypeInfo::TypeRef(s) => CG::Type::new(&to_struct_name(s, None)),
        _ => todo!(),
    }
}

/// creates a string representing the mask value
pub fn to_mask_str(m: u64, len: u64) -> String {
    match len {
        0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
        9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
        17..=32 => format!("0x{:08x}", (m & 0xffffffff) as u32),
        33..=64 => format!("0x{m:016x}"),
        _ => String::from("unknown"),
    }
}

/// writes the scope to a file or to stdout
pub fn save_scope(scope: CG::Scope, outdir: &Path, name: &str) -> Result<(), VelosiCodeGenError> {
    // set the path to the file
    let file = outdir.join(format!("{name}.rs"));

    // write the file, return IOError otherwise
    fs::write(file, scope.to_string().as_bytes())?;

    Ok(())
}

/// adds the header to the file
pub fn add_header(scope: &mut CG::Scope, title: &str) {
    // set the title of the file
    // construct the license
    let mut lic = CG::License::new(title, CG::LicenseType::Mit);
    lic.add_copyright(COPYRIGHT);

    // now add the license to the scope
    scope.license(lic);

    // adding the autogenerated warning
    scope.new_comment("THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER");
}

pub fn add_const_def(scope: &mut CG::Scope, c: &VelosiAstConst) {
    //
    // TODO:
    //  - here we should get the type information etc...
    //  - also it would be nice to get brief descriptions of what the constant represents
    let ty = if c.value.result_type().is_boolean() {
        "bool"
    } else {
        "u64"
    };
    let val = &c.value.to_string();

    // the constant value
    let mconst = scope.new_const(c.ident(), ty, val);

    // add some documentation
    mconst.doc(vec![
        &format!("Defined constant `{}`", c.ident()),
        "",
        &format!("@loc: {}", c.loc.loc()),
    ]);

    // make it public
    mconst.vis("pub");
}
