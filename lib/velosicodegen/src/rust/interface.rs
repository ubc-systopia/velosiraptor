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

use super::{field, utils};
use crate::VelosiCodeGenError;
use velosiast::{
    VelosiAstField, VelosiAstInterfaceField, VelosiAstInterfaceMemoryField,
    VelosiAstInterfaceMmioField, VelosiAstUnitSegment,
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

    st.derive("Copy");
    st.derive("Clone");

    for p in &unit.params {
        let doc = format!("Parameter '{}' in unit '{}'", p.ident(), unit.ident());
        let loc = format!("@loc: {}", p.loc.loc());
        let mut f = CG::Field::new(p.ident(), utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
        f.doc(vec![&doc, &loc]);
        st.push_field(f);
    }

    // Step 2:  add the implementation
    let imp = scope.new_impl(&ifname);

    // constructor
    utils::add_constructor(imp, &ifname, &unit.params);

    // getters
    for p in &unit.params {
        let getter = imp
            .new_fn(p.ident())
            .vis("pub")
            .arg_ref_self()
            .ret(utils::vrs_type_to_rust_type(&p.ptype.typeinfo));
        getter.line(format!("self.{}", p.ident()));
    }

    for f in unit.interface.fields() {
        generate_read_field(f, imp);
        generate_write_field(f, imp);
    }
}

fn generate_read_field(f: &Rc<VelosiAstInterfaceField>, imp: &mut CG::Impl) {
    let fname = format!("read_{}", f.ident());
    let field_type = field::field_type(f);

    let read_fn = imp
        .new_fn(&fname)
        .vis("pub")
        .doc(&format!("reads value from interface field '{}'", f.ident()))
        .arg_ref_self()
        .ret(&field_type);
    match f.as_ref() {
        VelosiAstInterfaceField::Memory(VelosiAstInterfaceMemoryField { base, offset, .. })
        | VelosiAstInterfaceField::Mmio(VelosiAstInterfaceMmioField { base, offset, .. }) => {
            read_fn
                .line(format!(
                    "let ptr = phys_to_virt(self.{} + {} * 0x8) as *mut {field_type};",
                    base.ident(),
                    offset
                ))
                .line("unsafe { *ptr }");
        }
        VelosiAstInterfaceField::Register(_) => {
            read_fn.line("// TODO: read register").line("todo!()");
        }
    }
}

fn generate_write_field(f: &Rc<VelosiAstInterfaceField>, imp: &mut CG::Impl) {
    let fname = format!("write_{}", f.ident());
    let field_type = field::field_type(f);

    let write_fn = imp
        .new_fn(&fname)
        .vis("pub")
        .doc(&format!(
            "writes value 'val' into interface field '{}'",
            f.ident()
        ))
        .arg_ref_self()
        .arg("val", &field_type);
    match f.as_ref() {
        VelosiAstInterfaceField::Memory(VelosiAstInterfaceMemoryField { base, offset, .. })
        | VelosiAstInterfaceField::Mmio(VelosiAstInterfaceMmioField { base, offset, .. }) => {
            write_fn
                .line(format!(
                    "let ptr = phys_to_virt(self.{} + {} * 0x8) as *mut {field_type};",
                    base.ident(),
                    offset
                ))
                .line("unsafe { *ptr = val }");
        }
        VelosiAstInterfaceField::Register(_) => {
            write_fn.line("// TODO: write register").line("todo!()");
        }
    }
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

    scope.import("crate::utils", "*");
    scope.import("crate::os", "*");

    // add imports to used fields
    for f in unit.interface.fields() {
        scope.import("super::fields", &field::field_type(f));
    }

    generate_interface(&mut scope, unit);

    // save the scope
    utils::save_scope(scope, outdir, "interface")
}
