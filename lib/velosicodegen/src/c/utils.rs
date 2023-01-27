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

use std::collections::HashMap;

// get the code generator
use crustal as C;

use velosiast::ast::{
    VelosiAstConst, VelosiAstExpr, VelosiAstField, VelosiAstFieldSlice, VelosiAstInterfaceField,
    VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField, VelosiAstInterfaceRegisterField,
    VelosiAstMethod, VelosiAstType, VelosiAstTypeInfo, VelosiAstUnitSegment,
    VelosiAstUnitStaticMap, VelosiOpExpr, VelosiOperation,
};

use crate::COPYRIGHT;

pub fn unit_struct_field_name(name: &str) -> String {
    format!("_{}", name.to_ascii_lowercase())
}

pub fn unit_struct_name(unit_name: &str) -> String {
    unit_name.to_lowercase()
}

pub fn unit_flags_type(unit: &VelosiAstUnitSegment) -> String {
    format!("{}_flags_t", unit.ident())
}

pub fn segment_struct_name(unit: &VelosiAstUnitSegment) -> String {
    unit_struct_name(unit.ident())
}

pub fn staticmap_struct_name(unit: &VelosiAstUnitStaticMap) -> String {
    unit_struct_name(unit.ident())
}

pub fn unit_type_name_str(unit: &str) -> String {
    format!("{}_t", unit.to_lowercase())
}

pub fn segment_type_name(unit: &VelosiAstUnitSegment) -> String {
    unit_type_name_str(unit.ident())
}

pub fn staticmap_type_name(unit: &VelosiAstUnitStaticMap) -> String {
    unit_type_name_str(unit.ident())
}

/// constructs the struct type name
pub fn field_struct_name(segment: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    format!("{}_{}", segment.ident().to_lowercase(), field.ident())
}

/// constructs the field type name for a given field.
pub fn field_type_name(segment: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    format!("{}__t", field_struct_name(segment, field))
}

pub fn field_mask_name(segment: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    format!(
        "{}_{}__MASK",
        segment.ident().to_uppercase(),
        field.ident().to_uppercase()
    )
}

pub fn if_field_wr_fn_name_str(unit_name: &str, fieldname: &str) -> String {
    format!("{}_{}__wr", unit_name.to_lowercase(), fieldname)
}

pub fn if_field_wr_fn_name(segment: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    if_field_wr_fn_name_str(segment.ident(), field.ident())
}

pub fn if_field_rd_fn_name_str(unit: &str, fieldname: &str) -> String {
    format!("{}_{}__rd", unit.to_lowercase(), fieldname)
}

pub fn if_field_rd_fn_name(segment: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    if_field_rd_fn_name_str(segment.ident(), field.ident())
}

pub fn if_field_wr_slice_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!("{}_{}_{}__wr", unit.to_lowercase(), field, slice)
}

pub fn if_field_wr_slice_fn_name(
    segment: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    sl: &VelosiAstFieldSlice,
) -> String {
    if_field_wr_slice_fn_name_str(segment.ident(), field.ident(), sl.ident())
}

pub fn if_field_rd_slice_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!("{}_{}_{}__rd", unit.to_lowercase(), field, slice)
}

pub fn if_field_rd_slice_fn_name(
    unit: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    sl: &VelosiAstFieldSlice,
) -> String {
    if_field_rd_slice_fn_name_str(unit.ident(), field.ident(), sl.ident())
}

pub fn field_slice_extract_fn_name_str(unit: &str, field: &str, sl: &str) -> String {
    format!("{}_{}__extract_{}", unit.to_lowercase(), field, sl)
}

pub fn field_slice_extract_fn_name(
    unit: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    sl: &VelosiAstFieldSlice,
) -> String {
    field_slice_extract_fn_name_str(unit.ident(), field.ident(), sl.ident())
}

pub fn field_slice_insert_fn_name_str(unit: &str, field: &str, sl: &str) -> String {
    format!(
        "{}_{}__insert_{}",
        unit.to_lowercase(),
        field.to_lowercase(),
        sl.to_lowercase()
    )
}

pub fn field_slice_insert_fn_name(
    unit: &VelosiAstUnitSegment,
    field: &dyn VelosiAstField,
    sl: &VelosiAstFieldSlice,
) -> String {
    field_slice_insert_fn_name_str(unit.ident(), field.ident(), sl.ident())
}

pub fn field_get_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__get_raw", unit.to_lowercase(), field)
}

pub fn field_get_raw_fn_name(unit: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    field_get_raw_fn_name_str(unit.ident(), field.ident())
}

pub fn field_set_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__set_raw", unit.to_lowercase(), field.to_lowercase())
}

pub fn field_set_raw_fn_name(unit: &VelosiAstUnitSegment, field: &dyn VelosiAstField) -> String {
    field_set_raw_fn_name_str(unit.ident(), field.ident())
}

pub fn op_fn_name(unit: &VelosiAstUnitSegment, op: &VelosiAstMethod) -> String {
    format!("{}_{}", unit.ident().to_lowercase(), op.ident())
}

pub fn translate_fn_name(unit_name: &str) -> String {
    format!("{}_resolve", unit_name.to_lowercase())
}

pub fn constructor_fn_name(unit_name: &str) -> String {
    format!("{}_init", unit_name.to_lowercase())
}

pub fn os_mmio_register_read_fn(
    unit_var: &C::Expr,
    field: &VelosiAstInterfaceMmioField,
) -> C::Expr {
    let fnname = format!("os_mmio_register_read_{}", field.nbits());
    let base = format!("_{}", field.base);

    C::Expr::fn_call(
        &fnname,
        vec![
            C::Expr::field_access(unit_var, &base),
            C::Expr::new_num(field.offset),
        ],
    )
}

pub fn os_mmio_register_write_fn(
    unit_var: &C::Expr,
    field: &VelosiAstInterfaceMmioField,
    val: &C::Expr,
) -> C::Expr {
    let fnname = format!("os_mmio_register_write_{}", field.nbits());
    let base = format!("_{}", field.base.as_str());

    C::Expr::fn_call(
        &fnname,
        vec![
            C::Expr::field_access(unit_var, &base),
            C::Expr::new_num(field.offset),
            val.clone(),
        ],
    )
}

pub fn os_register_write_fn(
    _unit_var: &C::Expr,
    field: &VelosiAstInterfaceRegisterField,
    val: &C::Expr,
) -> C::Expr {
    let fnname = format!("os_register_write_{}", field.nbits());

    C::Expr::fn_call(&fnname, vec![val.clone()])
}

pub fn os_register_read_fn(
    _unit_var: &C::Expr,
    field: &VelosiAstInterfaceRegisterField,
    val: &C::Expr,
) -> C::Expr {
    let fnname = format!("os_register_read_{}", field.nbits());

    C::Expr::fn_call(&fnname, vec![val.clone()])
}

pub fn os_memory_write_fn(
    unit_var: &C::Expr,
    field: &VelosiAstInterfaceMemoryField,
    val: &C::Expr,
) -> C::Expr {
    let fnname = format!("os_memory_write_{}", field.nbits());
    let base = format!("_{}", field.base.as_str());

    C::Expr::fn_call(
        &fnname,
        vec![
            C::Expr::field_access(unit_var, &base),
            C::Expr::new_num(field.offset),
            val.clone(),
        ],
    )
}

pub fn os_memory_read_fn(
    unit_var: &C::Expr,
    field: &VelosiAstInterfaceMemoryField,
    _val: &C::Expr,
) -> C::Expr {
    let fnname = format!("os_memory_read_{}", field.nbits());
    let base = format!("_{}", field.base);

    C::Expr::fn_call(
        &fnname,
        vec![
            C::Expr::field_access(unit_var, &base),
            C::Expr::new_num(field.offset),
        ],
    )
}

pub fn interface_write_fn(
    unit_var: &C::Expr,
    field: &VelosiAstInterfaceField,
    val: &C::Expr,
) -> C::Expr {
    match field {
        VelosiAstInterfaceField::Memory(mem) => os_memory_write_fn(unit_var, mem, val),
        VelosiAstInterfaceField::Register(reg) => {
            // cpu register
            os_register_write_fn(unit_var, reg, val)
        }
        VelosiAstInterfaceField::Mmio(mmio) => {
            // write to mmio register
            os_mmio_register_write_fn(unit_var, mmio, val)
        }
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
    scope.new_comment(title);
    scope.push_doc_str(COPYRIGHT);
    scope.new_comment("THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER");
}

pub fn add_const_def(scope: &mut C::Scope, c: &VelosiAstConst) {
    let mut m = C::Macro::new(c.ident());

    if c.value.result_type().is_numeric() {
        m.set_value(&format!("(uint64_t)({})", c));
    } else {
        m.set_value(&format!("{}", c));
    }

    // add some documentation
    m.doc_str(&format!("Defined constant `{}`", c.ident()));
    m.doc_str("");
    m.doc_str(&format!("@loc: {}", c.loc.loc()));

    scope.push_macro(m);
}

fn oparg_to_rust_expr(op: &VelosiOpExpr) -> Option<C::Expr> {
    match op {
        VelosiOpExpr::None => None,
        VelosiOpExpr::Num(x) => Some(C::Expr::new_num(*x)),
        VelosiOpExpr::Var(x) => Some(C::Expr::new_var(x, C::Type::new_int(64))),
        VelosiOpExpr::Shl(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "<<",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Shr(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            ">>",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::And(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "&",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Or(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "|",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Add(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "+",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Sub(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "-",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Mul(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "*",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Div(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "/",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Mod(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "%",
            oparg_to_rust_expr(y).unwrap(),
        )),
        VelosiOpExpr::Not(x) => Some(C::Expr::uop("!", oparg_to_rust_expr(x).unwrap())),
        VelosiOpExpr::Flags(v, f) => Some(C::Expr::field_access(
            &C::Expr::new_var(v, C::Type::new_typedef("dummy")),
            f,
        )),
    }
}

pub fn op_to_c_expr(
    unit: &str,
    c: &mut C::Block,
    op: &VelosiOperation,
    vars: &HashMap<String, C::Expr>,
) {
    match op {
        VelosiOperation::InsertSlice(field, slice, arg) => {
            let fname = field_slice_insert_fn_name_str(unit, field, slice);
            //format!("v_{}.insert_{}({});", field, slice, oparg_to_rust_expr(arg))
            let v = vars.get(field.as_str()).unwrap();
            let mut args = vec![v.clone()];
            if let Some(a) = oparg_to_rust_expr(arg) {
                args.push(a);
            }
            c.assign(v.clone(), C::Expr::fn_call(&fname, args));
        }
        VelosiOperation::InsertField(field, arg) => {
            let fname = field_set_raw_fn_name_str(unit, field);
            let v = vars.get(field.as_str()).unwrap();
            let mut args = Vec::new();
            if let Some(a) = oparg_to_rust_expr(arg) {
                args.push(a);
            }
            c.assign(v.clone(), C::Expr::fn_call(&fname, args));
        }
        VelosiOperation::ExtractSlice(field, slice) => {
            let fname = field_slice_extract_fn_name_str(unit, field, slice);
            c.fn_call(&fname, vec![]);
        }
        VelosiOperation::WriteActions(field) => {
            let fname = if_field_wr_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field.as_str()).unwrap();
            c.fn_call(&fname, vec![u.clone(), f.clone()]);
        }
        VelosiOperation::ReadActions(field) => {
            let fname = if_field_rd_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field.as_str()).unwrap();
            c.assign(f.clone(), C::Expr::fn_call(&fname, vec![u.clone()]));
        }
        VelosiOperation::Return => (),
    }
}

pub fn ptype_to_ctype(ptype: &VelosiAstType, unit: &VelosiAstUnitSegment) -> C::Type {
    match &ptype.typeinfo {
        VelosiAstTypeInfo::Integer => C::Type::new_typedef("uint64_t"),
        VelosiAstTypeInfo::Bool => C::Type::new_typedef("bool"),
        VelosiAstTypeInfo::GenAddr => C::Type::new_typedef("genaddr_t"),
        VelosiAstTypeInfo::VirtAddr => C::Type::new_typedef("vaddr_t"),
        VelosiAstTypeInfo::PhysAddr => C::Type::new_typedef("paddr_t"),
        VelosiAstTypeInfo::Size => C::Type::new_typedef("size_t"),
        VelosiAstTypeInfo::Flags => C::Type::new_typedef(&unit_flags_type(unit)),
        VelosiAstTypeInfo::TypeRef(s) => {
            let name = unit_type_name_str(s.as_str());
            C::Type::new_typedef(&name)
        }
        _ => todo!(),
    }
}

fn expr_to_cpp(_unit: &str, expr: &VelosiAstExpr) -> C::Expr {
    use VelosiAstExpr::*;
    match expr {
        IdentLiteral(_i) => panic!("don't know how to handle quantifier"),
        NumLiteral(_i) => panic!("don't know how to handle quantifier"),
        BoolLiteral(_i) => panic!("don't know how to handle quantifier"),
        BinOp(_i) => panic!("don't know how to handle quantifier"),
        UnOp(_i) => panic!("don't know how to handle quantifier"),
        Quantifier(_i) => panic!("don't know how to handle quantifier"),
        FnCall(_i) => panic!("don't know how to handle quantifier"),
        IfElse(_i) => panic!("don't know how to handle quantifier"),
        Slice(_i) => panic!("don't know how to handle slices"),
        Range(_i) => panic!("don't know how to handle quantifier"),
    }

    // use VelosiAstExpr::*;
    // match expr {
    //     Identifier { path, .. } => {
    //         match path[0].as_str() {
    //             "state" => {
    //                 // this->_state.control_field()
    //                 state_field_access(unit, &path[1..])
    //             }
    //             "interface" => panic!("state not implemented"),
    //             p => C::Expr::new_var(p, C::Type::new_int(64)),
    //         }
    //     }
    //     Number { value, .. } => C::Expr::new_num(*value),
    //     Boolean { value: true, .. } => C::Expr::btrue(),
    //     Boolean { value: false, .. } => C::Expr::bfalse(),
    //     BinaryOperation { op, lhs, rhs, .. } => {
    //         let o = format!("{}", op);
    //         let e = expr_to_cpp(unit, lhs);
    //         let e2 = expr_to_cpp(unit, rhs);
    //         C::Expr::binop(e, &o, e2)
    //     }
    //     UnaryOperation { op, val, .. } => {
    //         let o = format!("{}", op);
    //         let e = expr_to_cpp(unit, val);
    //         C::Expr::uop(&o, e)
    //     }
    //     FnCall { path, args, .. } => {
    //         if path.len() != 1 {
    //             panic!("TODO: handle multiple path components");
    //         }
    //         C::Expr::method_call(
    //             &C::Expr::this(),
    //             &path[0],
    //             args.iter().map(|x| expr_to_cpp(unit, x)).collect(),
    //         )
    //     }
    //     Slice { .. } => panic!("don't know how to handle slice"),
    //     Element { .. } => panic!("don't know how to handle element"),
    //     Range { .. } => panic!("don't know how to handle range"),
    //     Quantifier { .. } => panic!("don't know how to handle quantifier"),
    // }
}
