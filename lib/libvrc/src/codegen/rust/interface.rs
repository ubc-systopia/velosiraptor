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

use std::fs;
use std::path::Path;

use codegen_rs as CG;

use super::utils;
use crate::ast::{Interface, Unit};
use crate::codegen::rust::field;
use crate::codegen::CodeGenError;

/// returns the string of the field type
pub fn interface_type(unit: &Unit) -> String {
    utils::to_struct_name(&unit.name, Some("Interface"))
}

pub fn generate_memory_interface(scope: &mut CG::Scope, unit: &Unit) {
    let ifname = interface_type(unit);

    // Step 1:  add the struct definition, here we need to add all the fields

    let st = scope.new_struct(&ifname);
    st.vis("pub");
    st.doc(&format!(
        "Represents the interface of unit '{}' (memory).\n@loc: {}",
        unit.name,
        unit.location()
    ));
    // c representation
    st.repr("C");

    for f in unit.interface.fields() {
        let doc = format!("Field '{}' in unit '{}'", f.field.name, unit.name);
        let loc = format!("@loc: {}", f.field.location());
        let mut f = CG::Field::new(&f.field.name, field::field_type(&f.field));
        f.doc(vec![&doc, &loc]);
        st.push_field(f);
    }

    // Step 2:  add the implementation
    let imp = scope.new_impl(&ifname);

    for f in unit.interface.fields() {
        let fname = format!("write_{}", f.field.name);
        let body = format!("self.{} = val;", f.field.name);
        imp.new_fn(&fname)
            .vis("pub")
            .doc(&format!(
                "writes value 'val' into interface field '{}'",
                f.field.name
            ))
            .arg_mut_self()
            .arg("val", field::field_type(&f.field))
            .line(body);

        let fname = format!("read_{}", f.field.name);
        let body = format!("self.{}", f.field.name);
        imp.new_fn(&fname)
            .vis("pub")
            .doc(&format!(
                "writes value 'val' into interface field '{}'",
                f.field.name
            ))
            .arg_mut_self()
            .ret(CG::Type::new(&field::field_type(&f.field)))
            .line(body);
    }
}

pub fn generate_mmio_interface(scope: &mut CG::Scope, unit: &Unit) {
    // here we need to have a pointer for each parameter
    let st = scope.new_struct(&interface_type(unit));
    st.vis("pub");
    st.doc(&format!(
        "Represents the interface of unit '{}' (mmio).\n@loc: {}",
        unit.name,
        unit.location()
    ));
    // for each base, add a field
    for b in unit.interface.bases() {
        let doc = format!("Base pointer '{}' in unit '{}'", b, unit.name);
        let mut f = CG::Field::new(&b.name, "*mut u8");
        f.doc(vec![&doc]);
        st.push_field(f);
    }
}

pub fn generate_register_interface(scope: &mut CG::Scope, unit: &Unit) {
    // there is not really an interface here, so an empty struct
    let st = scope.new_struct(&interface_type(unit));
    st.vis("pub");
    st.doc(&format!(
        "Represents the interface of unit '{}' (register).\n@loc: {}",
        unit.name,
        unit.location()
    ));
}

/// generates the field types for the interface
pub fn generate_interface_fields(unit: &Unit, outdir: &Path) -> Result<(), CodeGenError> {
    let fieldsdir = outdir.join("fields");

    fs::create_dir_all(&fieldsdir)?;

    let fields = unit.interface.fields();

    // add the mod path
    let mut scope = CG::Scope::new();

    let title = format!("{} interface module", unit.name);
    utils::add_header(&mut scope, &title);
    for f in fields {
        let i = format!("mod {};", f.field.name.to_lowercase());
        scope.raw(&i);
    }

    for f in fields {
        let i = format!(
            "pub use {}::{};",
            f.field.name.to_lowercase(),
            field::field_type(&f.field)
        );
        scope.raw(&i);
    }

    // save the scope
    utils::save_scope(scope, &fieldsdir, "mod")?;

    let res: Result<(), CodeGenError> = Ok(());
    fields.iter().fold(res, |res: Result<(), CodeGenError>, e| {
        let r = field::generate(&unit.name, &e.field, &fieldsdir);
        if res.is_err() {
            res
        } else {
            r
        }
    })
}

/// generates the Unit definitions
pub fn generate(unit: &Unit, outdir: &Path) -> Result<(), CodeGenError> {
    // nothing to do if there is no interface
    // XXX: revise this with static maps maybe?
    if unit.interface.is_none() {
        return Ok(());
    }

    // generate the interface fields
    generate_interface_fields(unit, outdir)?;

    // the code generation scope
    let mut scope = CG::Scope::new();

    // add the header comments
    let title = format!("`{}` Interface definition ", unit.name);
    utils::add_header(&mut scope, &title);

    for f in unit.interface.fields() {
        scope.import("fields", &field::field_type(&f.field));
    }

    match unit.interface {
        Interface::None { .. } => panic!("should not reach here: Interface::None"),
        Interface::Memory { .. } => generate_memory_interface(&mut scope, unit),
        Interface::MMIORegisters { .. } => generate_mmio_interface(&mut scope, unit),
        _ => generate_register_interface(&mut scope, unit),
    }

    // save the scope
    utils::save_scope(scope, outdir, "interface")
}
