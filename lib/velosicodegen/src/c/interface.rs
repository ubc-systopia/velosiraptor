// Velosiraptor Code Generator
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! Interface Generation (C/CPP)

use std::fs;
use std::path::{Path, PathBuf};

use crustal as C;

use velosiast::{
    VelosiAst, VelosiAstField, VelosiAstFieldSlice, VelosiAstInterfaceField, VelosiAstTypeProperty,
    VelosiAstUnit,
};

use super::{
    field,
    utils::{FieldUtils, SliceUtils, UnitUtils},
};
use crate::VelosiCodeGenError;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Slice Access
////////////////////////////////////////////////////////////////////////////////////////////////////

fn generate_read_slice_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &dyn VelosiAstField,
    slice: &VelosiAstFieldSlice,
) {
    // create the function
    let mut f = C::Function::with_string(
        slice.to_rd_fn(unit, field),
        <&VelosiAstFieldSlice as SliceUtils<&VelosiAstUnit, &dyn VelosiAstField>>::to_c_type(
            &slice,
        ),
    );
    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "reads the value `{}.{}` from the interface",
        field.ident(),
        slice.ident()
    ));

    // add function paramters
    let unit_param = f.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
    let unit_var = unit_param.to_expr();

    // declare local variable for reading the field
    let fieldtype = C::Type::new_typedef(&field.to_type_name(unit));
    let field_var_decl = f.body().new_variable("val", fieldtype);
    let field_var = field_var_decl.to_expr();

    // read teh field value into local variable
    f.body()
        .assign(field_var.clone(), field.to_rd_fn_call(unit, unit_var));

    // return the extracted value
    f.body()
        .return_expr(slice.to_extract_fn_call(unit, field, field_var));

    // add the function to the scope
    scope.push_function(f);
}

fn generate_write_slice_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &dyn VelosiAstField,
    slice: &VelosiAstFieldSlice,
) {
    // create the function
    let mut f = C::Function::with_string(slice.to_wr_fn(unit, field), C::Type::new_void());
    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "writes the value `{}.{}` from the interface",
        field.ident(),
        slice.ident()
    ));

    // add the unit and value parameters
    let unit_param = f.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
    let unit_var = unit_param.to_expr();
    let val_param = f.new_param(
        "val",
        <&VelosiAstFieldSlice as SliceUtils<&VelosiAstUnit, &dyn VelosiAstField>>::to_c_type(
            &slice,
        ),
    );
    let val_var = val_param.to_expr();

    // declare the local variable for the field
    let fieldtype = C::Type::new_typedef(&field.to_type_name(unit));
    let field_var_decl = f.body().new_variable("field", fieldtype);
    let field_var = field_var_decl.to_expr();

    // read the field value
    f.body().assign(
        field_var.clone(),
        field.to_rd_fn_call(unit, unit_var.clone()),
    );

    // insert the field value
    f.body().assign(
        field_var.clone(),
        slice.to_insert_fn_call(unit, field, field_var.clone(), val_var),
    );

    // write the value to the field
    f.body()
        .fn_call(&field.to_wr_fn(unit), vec![unit_var, field_var]);

    // add function to the scope
    scope.push_function(f);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//Field Write/Read
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Generates the method to read the entire field
fn generate_read_field(scope: &mut C::Scope, unit: &VelosiAstUnit, field: &dyn VelosiAstField) {
    // define the function sigature
    let fieldtype = C::Type::new_typedef(&field.to_type_name(unit));
    let mut f = C::Function::with_string(field.to_rd_fn(unit), fieldtype.clone());
    f.set_static().set_inline();
    f.push_doc_str(&format!("reads the `{}` interface field", field.ident()));

    // add the function parametes
    let unit_param = f.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
    let unit_var = unit_param.to_expr();

    // body: declare local variable with the type of the field
    let field_var_decl = f.body().new_variable("val", fieldtype);
    let field_var = field_var_decl.to_expr();

    // assign to the declared variable
    let reg_read_fn = field.to_os_rd_fn(unit, &unit_var);
    f.body().assign(
        field_var.clone(),
        field.to_set_val_fn_call(unit, reg_read_fn),
    );

    // return the value
    f.body().return_expr(field_var);

    // add the function to the scope
    scope.push_function(f);
}

/// Generates the write method for the entire field
fn generate_write_field(scope: &mut C::Scope, unit: &VelosiAstUnit, field: &dyn VelosiAstField) {
    // adding the set value function
    let mut f = C::Function::with_string(field.to_wr_fn(unit), C::Type::new_void());
    f.set_static().set_inline();
    f.push_doc_str(&format!("writes the `{}` interface field", field.ident()));

    // add the function parameters
    let unit_param = f.new_param("unit", C::Type::to_ptr(&unit.to_ctype()));
    let unit_var = unit_param.to_expr();
    let val_param = f.new_param("val", field.to_ctype(unit));
    let val_var = val_param.to_expr();

    // call the write function
    let reg_write_fn = field.to_os_wr_fn(unit, &unit_var, &field.to_get_val_fn_call(unit, val_var));
    f.body().raw_expr(reg_write_fn);

    // add the function to the scope
    scope.push_function(f);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

/// generates the field types for the interface
fn generate_interface_field_accessors(
    scope: &mut C::Scope,
    unit: &VelosiAstUnit,
    field: &VelosiAstInterfaceField,
) -> Result<(), VelosiCodeGenError> {
    scope.new_comment("Reading interface fields");
    generate_read_field(scope, unit, field);
    for slice in field.layout() {
        generate_read_slice_fn(scope, unit, field, slice);
    }

    scope.new_comment("Writing interface fields");
    generate_write_field(scope, unit, field);
    for slice in field.layout() {
        generate_write_slice_fn(scope, unit, field, slice);
    }

    Ok(())
}

fn generate_unit_struct(scope: &mut C::Scope, unit: &VelosiAstUnit, osspec: &VelosiAst) {
    let env = osspec.osspec().unwrap();

    let fields = if env.has_map_protect_unmap() {
        let mut fields = Vec::new();
        for etype in env.extern_types.values() {
            if etype
                .properties
                .contains(&VelosiAstTypeProperty::Descriptor)
            {
                for field in &etype.fields {
                    fields.push(C::Field::with_string(
                        field.ident_to_string(),
                        unit.ptype_to_ctype(&field.ptype.typeinfo, false),
                    ));
                }
                break;
            }
        }

        fields.push(C::Field::with_string(
            "child".to_string(),
            C::Type::new_struct("TODO_child_type").to_ptr(),
        ));

        fields
    } else {
        unit.params_as_slice()
            .iter()
            .map(|x| C::Field::with_string(x.ident().to_string(), C::Type::new_uintptr()))
            .collect()
    };

    let sn = unit.to_struct_name();
    let mut s = C::Struct::with_fields(&sn, fields);

    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc().loc()));

    let stype = s.to_type();

    scope.push_struct(s);

    // adding a type def;
    let fieldtype = unit.to_type_name();
    scope.new_typedef(&fieldtype, stype);
}

/// generates the interface for a segment unit
fn generate_segment(
    unit: &VelosiAstUnit,
    osspec: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    let env = osspec.osspec().unwrap();

    let mut scope = unit.new_scope("Interface");

    // add the header guard
    let hdrguard = format!("{}_INTERFACE_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    if env.has_map_protect_unmap() {
        s.new_comment("Interface through OS provided API.");
    } else {
        // generate the unit struct
        generate_unit_struct(s, unit, osspec);

        // generate the interface
        if let Some(interface) = unit.interface() {
            // include all the field headers
            for f in interface.fields() {
                let fieldname = format!(
                    "{}/{}_field.h",
                    unit.ident().to_ascii_lowercase(),
                    f.ident()
                );
                s.new_include(&fieldname, false);
            }

            // add the OS support includes
            s.new_include("os_mmio.h", true);
            s.new_include("os_registers.h", true);
            s.new_include("os_memory.h", true);

            // generate the field accessors
            for f in interface.fields() {
                generate_interface_field_accessors(s, unit, f).expect("generation failed");
            }
        } else {
            s.new_comment("No interface defined for this unit.");
        }
    }

    // save the file
    let filename = format!("{}_interface.h", unit.ident().to_ascii_lowercase());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    // generate the interface fields
    if !env.has_map_protect_unmap() {
        if let Some(interface) = unit.interface() {
            let fieldspath = outdir.join(unit.ident().to_ascii_lowercase());
            fs::create_dir_all(&fieldspath)?;
            for f in interface.fields() {
                field::generate(unit, f, &fieldspath).expect("generation failed");
            }
        }
    }

    Ok(())
}

/// starts the interface code generation
pub fn generate(
    unit: &VelosiAstUnit,
    osspec: &VelosiAst,
    outdir: &mut PathBuf,
) -> Result<(), VelosiCodeGenError> {
    // create the unit dir
    let dirname = unit.ident().to_lowercase();

    // create the directory
    fs::create_dir_all(&outdir)?;

    if matches!(unit, VelosiAstUnit::Segment(_)) {
        generate_segment(unit, osspec, outdir)?;
    } else {
        // the other unit types don't have an interface
    }

    Ok(())
}
