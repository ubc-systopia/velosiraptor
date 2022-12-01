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
use std::path::Path;

use crustal as C;

use velosiast::ast::{
    VelosiAstField, VelosiAstFieldSlice, VelosiAstInterfaceField,
    VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField, VelosiAstInterfaceRegisterField,
    VelosiAstUnitSegment,
};


use super::{field, utils};
use crate::VelosiCodeGenError;

/// Generates the method to read
///
/// ## Generate function:
///
/// ```c
/// field_type_t read_mmio_register(unit_t *unit) {
///    field_type_t val;
///    val = field_set_raw(mmio_register_read(addr, offset));
///    return val;
/// }
/// ```
// fn generate_read_memory(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, field: &Field) {
//     // adding the get value function
//     let fnname = utils::if_field_rd_fn_name(unit, field);
//     let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
//     let mut f = C::Function::with_string(fnname, fieldtype.clone());

//     f.set_static().set_inline();
//     f.push_doc_str(&format!("reads the mmio register `{}`", field.name));

//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
//     let p = f.new_param("unit", unittype);
//     let unit_var = p.to_expr();

//     //  let unit_var = C::Expr::from_fn_param(p);
//     let field_var_decl = C::Variable::new("val", fieldtype);
//     let field_var = field_var_decl.to_expr();

//     let set_val_fn = utils::field_set_raw_fn_name(unit, field);
//     let reg_read_fn = utils::mmio_register_read_fn(&unit_var, field);
//     f.body()
//         .variable(field_var_decl)
//         .assign(
//             field_var.clone(),
//             C::Expr::fn_call(&set_val_fn, vec![reg_read_fn]),
//         )
//         .return_expr(field_var);
//     scope.push_function(f);
// }

// /// Generates the
// ///
// fn generate_write_memory(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, field: &Field) {
//     // adding the set value function
//     let fnname = utils::if_field_wr_fn_name(unit, field);
//     let mut f = C::Function::with_string(fnname, C::Type::new_void());

//     f.set_static().set_inline();
//     f.push_doc_str(&format!("writes the mmio register `{}`", field.name));

//     let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
//     let p = f.new_param("unit", unittype);
//     let unit_var = p.to_expr();
//     let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
//     let v = f.new_param("val", fieldtype);
//     let val_var = v.to_expr();

//     let get_val_fn = utils::field_get_raw_fn_name(unit, field);
//     f.body().raw_expr(utils::mmio_register_write_fn(
//         &unit_var,
//         field,
//         &C::Expr::fn_call(&get_val_fn, vec![val_var]),
//     ));

//     // let p = f.new_param("field");
//     // let lhs = C::Expr::from_fn_param(p);
//     // let v = f.new_param("val", C::Type::new_uint(field.nbits()));
//     // let rhs = C::Expr::from_fn_param(v);
//     scope.push_function(f);
// }

// pub fn generate_memory_interface(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
//     for if_field in unit.interface.fields() {
//         let field = &if_field.field;

//         generate_read_memory(scope, unit, field);
//         for sl in &field.layout {
//             generate_read_slice_fn(scope, unit, field, sl)
//         }

//         generate_write_memory(scope, unit, field);
//         for sl in &field.layout {
//             generate_write_slice_fn(scope, unit, field, sl);
//         }
//     }
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Slice Access
////////////////////////////////////////////////////////////////////////////////////////////////////

fn generate_read_slice_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    slice: &VelosiAstFieldSlice,
) {
    let fnname = utils::if_field_rd_slice_fn_name(unit, field, slice);

    let mut f = C::Function::with_string(fnname, C::Type::new_int(field.nbits()));

    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));

    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "reads the value `{}.{}` from the interface",
        field.ident(),
        slice.ident()
    ));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();

    let field_var_decl = C::Variable::new("val", fieldtype);
    let field_var = field_var_decl.to_expr();

    let get_val_fn = utils::if_field_rd_fn_name(unit, field);
    let extract_fn = utils::field_slice_extract_fn_name(unit, field, slice);

    f.body()
        .variable(field_var_decl)
        .assign(
            field_var.clone(),
            C::Expr::fn_call(&get_val_fn, vec![unit_var]),
        )
        .return_expr(C::Expr::fn_call(&extract_fn, vec![field_var]));
    scope.push_function(f);
}

fn generate_write_slice_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    slice: &VelosiAstFieldSlice,
) {
    let fnname = utils::if_field_wr_slice_fn_name(unit, field, slice);

    let mut f = C::Function::with_string(fnname, C::Type::new_void());

    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));

    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "writes the value `{}.{}` from the interface",
        field.ident(),
        slice.ident()
    ));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();

    let unittype = C::Type::new_int(slice.nbits());
    let p = f.new_param("val", unittype);
    let val_var = p.to_expr();

    let field_var_decl = C::Variable::new("field", fieldtype);
    let field_var = field_var_decl.to_expr();

    let get_val_fn = utils::if_field_rd_fn_name(unit, field);
    let insert_fn = utils::field_slice_insert_fn_name(unit, field, slice);
    let set_val_fn = utils::if_field_wr_fn_name(unit, field);

    f.body()
        .variable(field_var_decl)
        .assign(
            field_var.clone(),
            C::Expr::fn_call(&get_val_fn, vec![unit_var.clone()]),
        )
        .assign(
            field_var.clone(),
            C::Expr::fn_call(&insert_fn, vec![field_var.clone(), val_var]),
        )
        .fn_call(&set_val_fn, vec![unit_var, field_var]);
    scope.push_function(f);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// MMIO Register Interface Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Generates the method to read
///
/// ## Generate function:
///
/// ```c
/// field_type_t read_mmio_register(unit_t *unit) {
///    field_type_t val;
///    val = field_set_raw(mmio_register_read(addr, offset));
///    return val;
/// }
/// ```
fn generate_read_mmio_register(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &VelosiAstInterfaceMmioField,
) {
    // adding the get value function
    let fnname = utils::if_field_rd_fn_name(unit, field);
    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
    let mut f = C::Function::with_string(fnname, fieldtype.clone());

    f.set_static().set_inline();
    f.push_doc_str(&format!("reads the mmio register `{}`", field.ident()));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();

    //  let unit_var = C::Expr::from_fn_param(p);
    let field_var_decl = C::Variable::new("val", fieldtype);
    let field_var = field_var_decl.to_expr();

    let set_val_fn = utils::field_set_raw_fn_name(unit, field);
    let reg_read_fn = utils::os_mmio_register_read_fn(&unit_var, field);
    f.body()
        .variable(field_var_decl)
        .assign(
            field_var.clone(),
            C::Expr::fn_call(&set_val_fn, vec![reg_read_fn]),
        )
        .return_expr(field_var);
    scope.push_function(f);
}

/// Generates the
///
fn generate_write_mmio_register(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &VelosiAstInterfaceMmioField,
) {
    // adding the set value function
    let fnname = utils::if_field_wr_fn_name(unit, field);
    let mut f = C::Function::with_string(fnname, C::Type::new_void());

    f.set_static().set_inline();
    f.push_doc_str(&format!("writes the mmio register `{}`", field.ident()));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::segment_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();
    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
    let v = f.new_param("val", fieldtype);
    let val_var = v.to_expr();

    let get_val_fn = utils::field_get_raw_fn_name(unit, field);
    f.body().raw_expr(utils::os_mmio_register_write_fn(
        &unit_var,
        field,
        &C::Expr::fn_call(&get_val_fn, vec![val_var]),
    ));

    // let p = f.new_param("field");
    // let lhs = C::Expr::from_fn_param(p);
    // let v = f.new_param("val", C::Type::new_uint(field.nbits()));
    // let rhs = C::Expr::from_fn_param(v);
    scope.push_function(f);
}

pub fn generate_mmio_interface_field(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &VelosiAstInterfaceMmioField,
) {
    generate_read_mmio_register(scope, unit, field);
    for sl in &field.layout {
        generate_read_slice_fn(scope, unit, field, sl)
    }

    generate_write_mmio_register(scope, unit, field);
    for sl in &field.layout {
        generate_write_slice_fn(scope, unit, field, sl);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Memory Interface Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

fn generate_write_memory(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitSegment,
    _field: &VelosiAstInterfaceMemoryField,
) {
    panic!("not implemented");
}

fn generate_read_memory(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitSegment,
    _field: &VelosiAstInterfaceMemoryField,
) {
    panic!("not implemented");
}

pub fn generate_memory_interface_field(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &VelosiAstInterfaceMemoryField,
) {
    generate_read_memory(scope, unit, field);
    for sl in &field.layout {
        generate_read_slice_fn(scope, unit, field, sl)
    }

    generate_write_memory(scope, unit, field);
    for sl in &field.layout {
        generate_write_slice_fn(scope, unit, field, sl);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Register Interface Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

fn generate_write_register(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitSegment,
    _field: &VelosiAstInterfaceRegisterField,
) {
    panic!("not implemented");
}

fn generate_read_register(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitSegment,
    _field: &VelosiAstInterfaceRegisterField,
) {
    panic!("not implemented");
}

pub fn generate_register_interface_field(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    field: &VelosiAstInterfaceRegisterField,
) {
    generate_read_register(scope, unit, field);
    for sl in &field.layout {
        generate_read_slice_fn(scope, unit, field, sl)
    }

    generate_write_register(scope, unit, field);
    for sl in &field.layout {
        generate_write_slice_fn(scope, unit, field, sl);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Fields
////////////////////////////////////////////////////////////////////////////////////////////////////

/// generates the field types for the interface
fn generate_interface_fields(
    unit: &VelosiAstUnitSegment,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    let fields = unit.interface.fields();

    let res: Result<(), VelosiCodeGenError> = Ok(());
    fields
        .iter()
        .fold(res, |res: Result<(), VelosiCodeGenError>, field| {
            let r = field::generate(unit, field, outdir);
            if res.is_err() {
                res
            } else {
                r
            }
        })
}

fn generate_unit_struct(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    let fields = unit
        .params
        .iter()
        .map(|x| {
            let n = format!("_{}", x.ident());
            C::Field::with_string(n, C::Type::new_uintptr())
        })
        .collect();

    let sn = utils::segment_struct_name(unit);
    let mut s = C::Struct::with_fields(&sn, fields);

    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

    let stype = s.to_type();

    scope.push_struct(s);

    // adding a type def;
    let fieldtype = utils::segment_type_name(unit);
    scope.new_typedef(&fieldtype, stype);
}

/// generates the Unit definitions
pub fn generate(unit: &VelosiAstUnitSegment, outdir: &Path) -> Result<(), VelosiCodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Interface Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_INTERFACE_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    for f in unit.interface.fields() {
        let fieldname = format!("fields/{}_field.h", f.ident());
        s.new_include(&fieldname, false);
    }

    if unit.interface.is_none() {
        s.new_comment("No interface defined for this unit.");
    }

    s.new_include("os/mmio.h", true);
    s.new_include("os/registers.h", true);
    s.new_include("os/memory.h", true);

    for f in unit.interface.fields() {
        match f.as_ref() {
            VelosiAstInterfaceField::Memory(field) => {
                generate_memory_interface_field(s, unit, field);
            }
            VelosiAstInterfaceField::Register(field) => {
                generate_register_interface_field(s, unit, field);
            }
            VelosiAstInterfaceField::Mmio(field) => {
                generate_mmio_interface_field(s, unit, field);
            }
        }
    }

    generate_unit_struct(s, unit);

    scope.set_filename("interface.h");
    scope.to_file(outdir, true)?;

    // generate the interface fields
    let fieldspath = outdir.join("fields");
    fs::create_dir_all(&fieldspath)?;
    generate_interface_fields(unit, &fieldspath)
}
