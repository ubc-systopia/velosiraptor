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

//! Interface Generation (Rust)

use std::path::Path;
use std::{fs, rc::Rc};

use codegen_rs as CG;

use super::utils::to_rust_type;
use super::{field, utils};
use crate::VelosiCodeGenError;
use velosiast::{
    VelosiAstField, VelosiAstFieldSlice, VelosiAstInterfaceField, VelosiAstUnitSegment,
};

/// returns the string of the field type
pub fn interface_type(unit: &VelosiAstUnitSegment) -> String {
    utils::to_struct_name(unit.ident(), Some("Interface"))
}

pub fn generate_interface(scope: &mut CG::Scope, unit: &VelosiAstUnitSegment) {
    let ifname = interface_type(unit);

    // Step 1:  add the struct definition, here we need to add all the fields

    let st = scope.new_struct(&ifname);
    st.vis("pub");
    st.doc(&format!(
        "Represents the interface of unit '{}'.\n@loc: {}",
        unit.ident(),
        unit.loc.loc(),
    ));
    // c representation
    st.repr("C");

    for f in unit.interface.fields() {
        let doc = format!("Field '{}' in unit '{}'", f.ident(), unit.ident());
        let loc = format!("@loc: {}", f.loc().loc());
        let mut f = CG::Field::new(f.ident(), field::field_type(f));
        f.doc(vec![&doc, &loc]);
        st.push_field(f);
    }

    // Step 2:  add the implementation
    let imp = scope.new_impl(&ifname);

    let iftyperef = "&'static Self";
    imp.new_fn("from_addr")
        .vis("pub")
        .arg("base", "u64")
        .doc(&format!(
            "creates a new reference to a {} interface",
            unit.ident()
        ))
        .ret(CG::Type::new(&iftyperef))
        .set_unsafe(true)
        .line("let ptr = base as *mut Self;")
        .line("ptr.as_ref().unwrap()");

    for f in unit.interface.fields() {
        generate_read_field(f, imp);
        generate_write_field(f, imp);

        for slice in f.layout() {
            generate_read_slice(f, slice, imp);
            generate_write_slice(f, slice, imp);
        }
    }
}

fn generate_read_field(f: &Rc<VelosiAstInterfaceField>, imp: &mut CG::Impl) {
    let fname = format!("read_{}", f.ident());
    let body = format!("self.{}", f.ident());
    imp.new_fn(&fname)
        .vis("pub")
        .doc(&format!("reads value from interface field '{}'", f.ident()))
        .arg_mut_self()
        .ret(CG::Type::new(&field::field_type(f)))
        .line(body);
}

fn generate_read_slice(
    f: &Rc<VelosiAstInterfaceField>,
    slice: &Rc<VelosiAstFieldSlice>,
    imp: &mut CG::Impl,
) {
    let fname = format!("read_{}_{}", f.ident(), slice.ident());
    let body = format!("self.{}.extract_{}()", f.ident(), slice.ident());
    let ftype = to_rust_type(slice.nbits());
    imp.new_fn(&fname)
        .vis("pub")
        .doc(&format!(
            "reads value from interface slice '{}'",
            slice.ident()
        ))
        .arg_mut_self()
        .ret(CG::Type::new(ftype))
        .line(body);
}

fn generate_write_field(f: &Rc<VelosiAstInterfaceField>, imp: &mut CG::Impl) {
    let fname = format!("write_{}", f.ident());
    let body = format!("self.{} = val;", f.ident());
    imp.new_fn(&fname)
        .vis("pub")
        .doc(&format!(
            "writes value 'val' into interface field '{}'",
            f.ident()
        ))
        .arg_mut_self()
        .arg("val", field::field_type(f))
        .line(body);
}

fn generate_write_slice(
    f: &Rc<VelosiAstInterfaceField>,
    slice: &Rc<VelosiAstFieldSlice>,
    imp: &mut CG::Impl,
) {
    let fname = format!("write_{}_{}", f.ident(), slice.ident());
    let body = format!("self.{}.insert_{}(val);", f.ident(), slice.ident());
    let ftype = to_rust_type(slice.nbits());
    imp.new_fn(&fname)
        .vis("pub")
        .doc(&format!(
            "writes value 'val' into interface slice '{}'",
            slice.ident()
        ))
        .arg_mut_self()
        .arg("val", ftype)
        .line(body);
}

/// generates the field types for the interface
pub fn generate_interface_fields(
    unit: &VelosiAstUnitSegment,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    let fieldsdir = outdir.join("fields");

    fs::create_dir_all(&fieldsdir)?;

    let fields = unit.interface.fields();

    // add the mod path
    let mut scope = CG::Scope::new();

    let title = format!("{} interface module", unit.ident());
    utils::add_header(&mut scope, &title);
    for f in fields {
        let i = format!("mod {};", f.ident().to_lowercase());
        scope.raw(&i);
    }

    for f in fields {
        let i = format!("pub use {}::*;", f.ident().to_lowercase());
        scope.raw(&i);
    }

    // save the scope
    utils::save_scope(scope, &fieldsdir, "mod")?;

    let res: Result<(), VelosiCodeGenError> = Ok(());
    fields
        .iter()
        .fold(res, |res: Result<(), VelosiCodeGenError>, e| {
            let r = field::generate(unit.ident(), e, &fieldsdir);
            if res.is_err() {
                res
            } else {
                r
            }
        })
}

/// generates the Unit definitions
pub fn generate(unit: &VelosiAstUnitSegment, outdir: &Path) -> Result<(), VelosiCodeGenError> {
    // generate the interface fields
    generate_interface_fields(unit, outdir)?;

    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("`{}` Interface definition ", unit.ident());
    utils::add_header(&mut scope, &title);

    for f in unit.interface.fields() {
        scope.import("super::fields", &field::field_type(f));
    }

    generate_interface(&mut scope, unit);

    // save the scope
    utils::save_scope(scope, outdir, "interface")
}
