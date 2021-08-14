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
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

// get the code generator
use codegen_rs as CG;

/// converts a string slice into a rustified string name
/// field_name  --> struct FieldName
pub fn to_struct_name(s: &str, suffix: Option<&str>) -> String {
    let mut c = s.chars();
    let mut s = match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
    .replace("_", "");

    if let Some(x) = suffix {
        s.push_str(x);
    }
    s
}

/// converts a string slice into a rusified constant identifier
pub fn to_const_name(s: &str) -> String {
    String::from(s.to_uppercase())
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

/// creates a strng reprsenting the mask value
pub fn to_mask_str(m: u64, len: u64) -> String {
    match len {
        0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
        9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
        17..=32 => format!("0x{:08x}", (m & 0xffffffff) as u32),
        33..=64 => format!("0x{:016x}", (m & 0xffffffffffffffff) as u64),
        _ => String::from("unknown"),
    }
}

/// writes the scope to a file or to stdout
pub fn save_scope(scope: CG::Scope, outdir: &Option<PathBuf>, name: &str) {
    if let Some(p) = outdir {
        // the root directory
        let outfile = p.join(format!("{}.rs", name));
        let mut rustfile = File::create(outfile).unwrap();
        rustfile.write_all(scope.to_string().as_bytes()).unwrap();
        rustfile.flush().unwrap();
    } else {
        println!("{:?}", scope.to_string())
    }
}
