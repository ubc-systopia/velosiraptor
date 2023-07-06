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

//! Synthesis Module: Smt2 Expressions

use velosiast::ast::{VelosiAstType, VelosiAstTypeInfo};

use smt2::{Function, Smt2Context, Sort, Term};

use super::{
    utils,
    velosimodel::{IFACE_PREFIX, STATE_PREFIX},
};

pub const DEFAULT_BIT_WIDTH: u64 = 64;

pub fn model(prefix: &str) -> String {
    utils::with_prefix(prefix, "Model_t")
}

pub fn iface(prefix: &str) -> String {
    utils::with_prefix(prefix, "IFace_t")
}

pub fn state(prefix: &str) -> String {
    utils::with_prefix(prefix, "State_t")
}

pub fn wbuffer(prefix: &str) -> String {
    utils::with_prefix(prefix, "WBuffer_t")
}

pub fn wbuffer_entry(prefix: &str) -> String {
    utils::with_prefix(prefix, "WBufferEntry_t")
}

pub fn field_tag(prefix: &str) -> String {
    utils::with_prefix(prefix, "FieldTag_t")
}

pub fn field_tag_enum(fieldname: &str) -> String {
    let mut enum_name = fieldname.to_string();
    enum_name.get_mut(0..1).unwrap().make_ascii_uppercase();
    enum_name
}

pub fn ctxt(prefix: &str, c: &str) -> String {
    utils::with_prefix(prefix, &format!("{c}_t"))
}

pub fn num(prefix: &str) -> String {
    utils::with_prefix(prefix, &String::from("Num"))
}

pub fn boolean() -> String {
    String::from("Bool")
}

pub fn addr(prefix: &str) -> String {
    utils::with_prefix(prefix, "Addr_t")
}

pub fn vaddr(prefix: &str) -> String {
    utils::with_prefix(prefix, "VAddr_t")
}

pub fn paddr(prefix: &str) -> String {
    utils::with_prefix(prefix, "PAddr_t")
}

pub fn size(prefix: &str) -> String {
    utils::with_prefix(prefix, "Size_t")
}

pub fn flags(prefix: &str) -> String {
    utils::with_prefix(prefix, "Flags_t")
}

pub fn field_type(prefix: &str, ctxt: &str, name: &str) -> String {
    let mut i = name.split('.');
    let ty = match (i.next(), i.next()) {
        (Some("state"), Some(name)) => format!("{STATE_PREFIX}Field.{name}_t"),
        (Some("interface"), Some(name)) => format!("{IFACE_PREFIX}Field.{name}_t"),
        (Some(name), None) => format!("{ctxt}Field.{name}_t"),
        _ => panic!("{} {}", ctxt, name),
    };
    utils::with_prefix(prefix, &ty)
}

pub fn add_type_def(smt: &mut Smt2Context, name: String, sort: String) {
    let sort = Sort::new_def(name, sort);
    smt.sort(sort);
}

pub fn add_type_constraints(smt: &mut Smt2Context, name: String, maxbits: u64) {
    let fnname = format!("{name}.assms");
    let mut f = Function::new(fnname, boolean());
    f.add_comment(format!("Type constraints {name}"));
    f.add_arg(String::from("v"), name);

    let body = if maxbits == DEFAULT_BIT_WIDTH {
        Term::binary(true)
    } else {
        let maxval = (1 << maxbits) - 1;
        Term::land(
            Term::bvge(Term::ident("v".to_string()), Term::num(0)),
            Term::bvle(Term::ident("v".to_string()), Term::num(maxval)),
        )
    };

    f.add_body(body);
    smt.function(f);
}

fn add_type_constraints_size(smt: &mut Smt2Context, name: String, maxbits: u64) {
    let fnname = format!("{name}.assms");
    let mut f = Function::new(fnname, boolean());
    f.add_comment(format!("Type constraints {name}"));
    f.add_arg(String::from("v"), name);

    let body = if maxbits == DEFAULT_BIT_WIDTH {
        Term::binary(true)
    } else {
        let maxval = 1 << maxbits;
        Term::land(
            Term::bvge(Term::ident("v".to_string()), Term::num(0)),
            Term::bvle(Term::ident("v".to_string()), Term::num(maxval)),
        )
    };

    f.add_body(body);
    smt.function(f);
}

pub fn add_type_defs(smt: &mut Smt2Context, prefix: &str, inaddr: u64, outaddr: u64) {
    smt.section(String::from("Type Definitions"));

    let default_sort = format!("(_ BitVec {DEFAULT_BIT_WIDTH})");
    add_type_def(smt, num(prefix), default_sort.clone());
    add_type_def(smt, addr(prefix), default_sort.clone());
    add_type_def(smt, vaddr(prefix), default_sort.clone());
    add_type_def(smt, paddr(prefix), default_sort.clone());
    add_type_def(smt, size(prefix), default_sort.clone());
    add_type_def(smt, flags(prefix), default_sort);

    add_type_constraints(smt, addr(prefix), DEFAULT_BIT_WIDTH);
    add_type_constraints(smt, vaddr(prefix), inaddr);
    add_type_constraints(smt, paddr(prefix), outaddr);
    add_type_constraints(smt, flags(prefix), DEFAULT_BIT_WIDTH);

    add_type_constraints_size(smt, size(prefix), std::cmp::min(inaddr, outaddr));
}

/// Obtains the type information of the
pub fn typeinfo_to_smt2(prefix: &str, ty: &VelosiAstTypeInfo) -> String {
    use VelosiAstTypeInfo::*;
    match ty {
        // built-in integer type
        Integer => num(prefix),
        // built-in boolean type
        Bool => boolean(),
        // built-in generic address type
        GenAddr => addr(prefix),
        // built-in virtual address type
        VirtAddr => vaddr(prefix),
        // built-in physical address type
        PhysAddr => paddr(prefix),
        // built-in size type
        Size => size(prefix),
        // built-in flags type
        Flags => flags(prefix),
        // built in range type
        Range => unimplemented!("don't know how to handle ranges yet"),
        // type referece to user-define type
        TypeRef(_s) => {
            // here we just return the paddr instead.
            paddr(prefix)
            //unimplemented!("don't know how to handle typerefs yet ({s})"),
        }
        // Reference to the state
        State => panic!("state type not expected here"),
        // Reference to the interface
        Interface => panic!("interface type not expected here"),
        // Huh
        Void => panic!("void type not expected here"),
    }
}

pub fn type_to_smt2(prefix: &str, ty: &VelosiAstType) -> String {
    typeinfo_to_smt2(prefix, &ty.typeinfo)
}

pub fn type_to_assms_fn_name(prefix: &str, ty: &VelosiAstType) -> String {
    format!("{}.assms", type_to_smt2(prefix, ty))
}

pub fn type_to_assms_fn(prefix: &str, ty: &VelosiAstType, var: String) -> Term {
    let fname = type_to_assms_fn_name(prefix, ty);
    Term::fn_apply(fname, vec![Term::ident(var)])
}
