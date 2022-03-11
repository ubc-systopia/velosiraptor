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

use super::utils;
use crate::ast::{BitSlice, Field, Interface, Unit};
use crate::codegen::c::field;
use crate::codegen::CodeGenError;

pub fn generate_memory_interface(_scope: &mut C::Scope, _unit: &Unit) {
    //     let ifname = interface_type(unit);

    //     // Step 1:  add the struct definition, here we need to add all the fields

    //     let st = scope.new_struct(&ifname);
    //     st.vis("pub");
    //     st.doc(&format!(
    //         "Represents the interface of unit '{}' (memory).\n@loc: {}",
    //         unit.name,
    //         unit.location()
    //     ));
    //     // c representation
    //     st.repr("C");

    //     for f in unit.interface.fields() {
    //         let doc = format!("Field '{}' in unit '{}'", f.field.name, unit.name);
    //         let loc = format!("@loc: {}", f.field.location());
    //         let mut f = CG::Field::new(&f.field.name, field::field_type_name(&f.field));
    //         f.doc(vec![&doc, &loc]);
    //         st.push_field(f);
    //     }

    //     // Step 2:  add the implementation
    //     let imp = scope.new_impl(&ifname);

    //     let iftyperef = format!("&'static {}", ifname);
    //     imp.new_fn("from_addr")
    //         .vis("pub")
    //         .arg("base", "u64")
    //         .doc(&format!(
    //             "creates a new reference to a {} interface",
    //             unit.name
    //         ))
    //         .ret(CG::Type::new(&iftyperef))
    //         .set_unsafe(true)
    //         .line(format!("let ptr = base as *mut {};", iftyperef))
    //         .line("ptr.as_ref().unwrap()");

    //     for f in unit.interface.fields() {
    //         let fname = format!("write_{}", f.field.name);
    //         let body = format!("self.{} = val;", f.field.name);
    //         imp.new_fn(&fname)
    //             .vis("pub")
    //             .doc(&format!(
    //                 "writes value 'val' into interface field '{}'",
    //                 f.field.name
    //             ))
    //             .arg_mut_self()
    //             .arg("val", field::field_type_name(&f.field))
    //             .line(body);

    //         let fname = format!("read_{}", f.field.name);
    //         let body = format!("self.{}", f.field.name);
    //         imp.new_fn(&fname)
    //             .vis("pub")
    //             .doc(&format!(
    //                 "writes value 'val' into interface field '{}'",
    //                 f.field.name
    //             ))
    //             .arg_mut_self()
    //             .ret(CG::Type::new(&field::field_type_name(&f.field)))
    //             .line(body);
    //     }
}

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
fn generate_read_mmio_register(scope: &mut C::Scope, unit: &Unit, field: &Field) {
    // adding the get value function
    let fnname = utils::if_field_rd_fn_name(unit, field);
    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
    let mut f = C::Function::with_string(fnname, fieldtype.clone());

    f.set_static().set_inline();
    f.push_doc_str(&format!("reads the mmio register `{}`", field.name));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();

    //  let unit_var = C::Expr::from_fn_param(p);
    let field_var_decl = C::Variable::new("val", fieldtype);
    let field_var = field_var_decl.to_expr();

    let set_val_fn = utils::field_set_raw_fn_name(unit, field);
    let reg_read_fn = utils::mmio_register_read_fn(&unit_var, field);
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
fn generate_write_mmio_register(scope: &mut C::Scope, unit: &Unit, field: &Field) {
    // adding the set value function
    let fnname = utils::if_field_wr_fn_name(unit, field);
    let mut f = C::Function::with_string(fnname, C::Type::new_void());

    f.set_static().set_inline();
    f.push_doc_str(&format!("writes the mmio register `{}`", field.name));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit)));
    let p = f.new_param("unit", unittype);
    let unit_var = p.to_expr();
    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));
    let v = f.new_param("val", fieldtype);
    let val_var = v.to_expr();

    let get_val_fn = utils::field_get_raw_fn_name(unit, field);
    f.body().raw_expr(utils::mmio_register_write_fn(
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

fn generate_read_slice_mmio(scope: &mut C::Scope, unit: &Unit, field: &Field, slice: &BitSlice) {
    let fnname = utils::if_field_rd_slice_fn_name(unit, field, slice);

    let mut f = C::Function::with_string(fnname, C::Type::new_int(field.nbits()));

    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));

    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "reads the value `{}.{}` from the interface",
        field.name, slice.name
    ));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit)));
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

fn generate_write_slice_mmio(scope: &mut C::Scope, unit: &Unit, field: &Field, slice: &BitSlice) {
    let fnname = utils::if_field_wr_slice_fn_name(unit, field, slice);

    let mut f = C::Function::with_string(fnname, C::Type::new_void());

    let fieldtype = C::Type::new_typedef(&utils::field_type_name(unit, field));

    f.set_static().set_inline();
    f.push_doc_str(&format!(
        "writes the value `{}.{}` from the interface",
        field.name, slice.name
    ));

    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit)));
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

pub fn generate_mmio_interface(scope: &mut C::Scope, unit: &Unit) {
    for if_field in unit.interface.fields() {
        let field = &if_field.field;

        generate_read_mmio_register(scope, unit, field);
        for sl in &field.layout {
            generate_read_slice_mmio(scope, unit, field, sl)
        }

        generate_write_mmio_register(scope, unit, field);
        for sl in &field.layout {
            generate_write_slice_mmio(scope, unit, field, sl);
        }
    }
}

pub fn generate_register_interface(_scope: &mut C::Scope, _unit: &Unit) {
    // there is not really an interface here, so an empty struct
    // let st = scope.new_struct(&interface_type(unit));
    // st.vis("pub");
    // st.doc(&format!(
    //     "Represents the interface of unit '{}' (register).\n@loc: {}",
    //     unit.name,
    //     unit.location()
    // ));
}

/// generates the field types for the interface
pub fn generate_interface_fields(unit: &Unit, outdir: &Path) -> Result<(), CodeGenError> {
    let fields = unit.interface.fields();

    let res: Result<(), CodeGenError> = Ok(());
    fields.iter().fold(res, |res: Result<(), CodeGenError>, e| {
        let r = field::generate(unit, &e.field, outdir);
        if res.is_err() {
            res
        } else {
            r
        }
    })
}

fn generate_unit_struct(scope: &mut C::Scope, unit: &Unit) {
    let fields = unit
        .params
        .iter()
        .map(|x| {
            let n = format!("_{}", x.name);
            C::Field::with_string(n, C::Type::new_uintptr())
        })
        .collect();

    let sn = utils::unit_struct_name(unit);
    let mut s = C::Struct::with_fields(&sn, fields);

    s.push_doc_str(&format!("Unit Type `{}`", unit.name));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.location()));

    let stype = s.to_type();

    scope.push_struct(s);

    // adding a type def;
    let fieldtype = utils::unit_type_name(unit);
    scope.new_typedef(&fieldtype, stype);
}

/// generates the Unit definitions
pub fn generate(unit: &Unit, outdir: &Path) -> Result<(), CodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Interface Definitions for `{}`", unit.name);
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_INTERFACE_H_", unit.name.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    for f in unit.interface.fields() {
        let fieldname = format!("fields/{}_field.h", f.field.name);
        s.new_include(&fieldname, false);
    }

    s.new_include("mmio.h", true);

    generate_unit_struct(s, unit);

    match unit.interface {
        Interface::None { .. } => {
            s.new_comment("No interface defined for this unit.");
        }
        Interface::Memory { .. } => {
            generate_memory_interface(s, unit);
        }
        Interface::MMIORegisters { .. } => {
            generate_mmio_interface(s, unit);
        }
        Interface::CPURegisters { .. } => {
            generate_register_interface(s, unit);
        }
        _ => panic!("Unsupported interface type"),
    }

    scope.set_filename("interface.h");
    scope.to_file(outdir, true)?;

    // generate the interface fields
    let fieldspath = outdir.join("fields");
    fs::create_dir_all(&fieldspath)?;
    generate_interface_fields(unit, &fieldspath)
}
