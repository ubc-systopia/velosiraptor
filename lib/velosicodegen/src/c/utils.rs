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
    VelosiAstBinOp, VelosiAstConst, VelosiAstExpr, VelosiAstField, VelosiAstFieldSlice,
    VelosiAstInterfaceField, VelosiAstInterfaceMemoryField, VelosiAstInterfaceMmioField,
    VelosiAstInterfaceRegisterField, VelosiAstMethod, VelosiAstTypeInfo, VelosiAstUnOp,
    VelosiAstUnit, VelosiAstUnitEnum, VelosiAstUnitSegment, VelosiAstUnitStaticMap, VelosiOpExpr,
    VelosiOperation,
};

use crate::COPYRIGHT;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Unit Utilities
////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn unit_type_str(ident: &str) -> String {
    format!("{}__t", ident.to_ascii_lowercase())
}

pub fn flags_type_str(unit: &str) -> String {
    format!("{}_flags__t", unit.to_ascii_lowercase())
}

pub fn unit_struct_field_name(name: &str) -> String {
    format!("_{}", name.to_ascii_lowercase())
}

pub trait UnitUtils {
    /// returns the identifier of the unit
    fn my_ident(&self) -> &str;

    /// returns the type name of the unit `myunit_t`
    fn to_type_name(&self) -> String {
        unit_type_str(self.my_ident())
    }

    fn to_ctype(&self) -> C::Type {
        C::Type::new_typedef(&self.to_type_name())
    }

    /// returns the struct name of the unit `myunit`
    fn to_struct_name(&self) -> String {
        self.my_ident().to_ascii_lowercase()
    }

    /// returns the type name for the unit's flags `myunit_flags_t`
    fn to_flags_type(&self) -> String {
        flags_type_str(self.my_ident())
    }

    fn to_flags_struct_name(&self) -> String {
        format!("{}_flags", self.my_ident().to_ascii_lowercase())
    }

    fn to_op_fn_name(&self, op: &VelosiAstMethod) -> String {
        format!("{}_{}", self.my_ident().to_ascii_lowercase(), op.ident())
    }

    fn translate_fn_name(&self) -> String {
        format!("{}_resolve", self.my_ident().to_ascii_lowercase())
    }

    fn constructor_fn_name(&self) -> String {
        format!("{}_init", self.my_ident().to_ascii_lowercase())
    }

    fn new_scope(&self, title: &str) -> C::Scope {
        // the code generation scope
        let mut scope = C::Scope::new();

        // constant definitions
        let title = format!("{} Definitions for `{}`", title, self.my_ident());
        add_header(&mut scope, &title);

        scope
    }

    fn ptype_to_ctype(&self, ptype: &VelosiAstTypeInfo) -> C::Type {
        match ptype {
            VelosiAstTypeInfo::Integer => C::Type::new_uint64(),
            VelosiAstTypeInfo::Bool => C::Type::new_bool(),
            VelosiAstTypeInfo::GenAddr => C::Type::new_typedef("genaddr_t"),
            VelosiAstTypeInfo::VirtAddr => C::Type::new_typedef("vaddr_t"),
            VelosiAstTypeInfo::PhysAddr => C::Type::new_typedef("paddr_t"),
            VelosiAstTypeInfo::Size => C::Type::new_typedef("size_t"),
            VelosiAstTypeInfo::Flags => C::Type::new_typedef(&self.to_flags_type()),
            VelosiAstTypeInfo::TypeRef(s) => {
                let name = unit_type_str(s.as_str());
                C::Type::new_typedef(&name)
            }
            _ => todo!(),
        }
    }

    fn expr_to_cpp(&self, expr: &VelosiAstExpr) -> C::Expr {
        use VelosiAstExpr::*;
        match expr {
            IdentLiteral(i) => {
                C::Expr::new_var(i.ident().as_str(), self.ptype_to_ctype(expr.result_type()))
            }
            NumLiteral(i) => C::Expr::new_num(i.val),
            BoolLiteral(i) => {
                if i.val {
                    C::Expr::btrue()
                } else {
                    C::Expr::bfalse()
                }
            }
            BinOp(i) => match i.op {
                VelosiAstBinOp::LShift => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "<<", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::RShift => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), ">>", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::And => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "&", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Or => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "|", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Xor => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "^", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Plus => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "+", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Minus => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "-", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Multiply => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "*", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Divide => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "/", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Modulo => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "%", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Eq => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "==", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Ne => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "!=", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Lt => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "<", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Gt => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), ">", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Le => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "<=", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Ge => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), ">=", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Land => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "&&", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Lor => {
                    C::Expr::binop(self.expr_to_cpp(&i.lhs), "||", self.expr_to_cpp(&i.rhs))
                }
                VelosiAstBinOp::Implies => C::Expr::binop(
                    C::Expr::uop("!", self.expr_to_cpp(&i.lhs)),
                    "||",
                    self.expr_to_cpp(&i.rhs),
                ),
            },
            UnOp(i) => match i.op {
                VelosiAstUnOp::Not => C::Expr::uop("~", self.expr_to_cpp(&i.expr)),
                VelosiAstUnOp::LNot => C::Expr::uop("!", self.expr_to_cpp(&i.expr)),
            },
            Quantifier(_i) => panic!("don't know how to handle quantifier"),
            FnCall(i) => C::Expr::fn_call(i.ident(), vec![]),
            IfElse(_i) => panic!("don't know how to handle ifelse"),
            Slice(_i) => panic!("don't know how to handle slices"),
            Range(_i) => panic!("don't know how to handle range"),
        }
    }
}

impl UnitUtils for &VelosiAstUnit {
    fn my_ident(&self) -> &str {
        self.ident()
    }
}

impl UnitUtils for &VelosiAstUnitSegment {
    fn my_ident(&self) -> &str {
        self.ident()
    }
}

impl UnitUtils for &VelosiAstUnitStaticMap {
    fn my_ident(&self) -> &str {
        self.ident()
    }
}

impl UnitUtils for &VelosiAstUnitEnum {
    fn my_ident(&self) -> &str {
        self.ident()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Field Utils
////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn field_wr_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__wr", unit.to_lowercase(), field.to_lowercase())
}

pub fn field_rd_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__rd", unit.to_lowercase(), field.to_lowercase())
}

pub fn field_get_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__get_raw", unit.to_lowercase(), field)
}

pub fn field_set_raw_fn_name_str(unit: &str, field: &str) -> String {
    format!("{}_{}__set_raw", unit.to_lowercase(), field.to_lowercase())
}

pub trait FieldUtils<U>
where
    U: UnitUtils,
{
    /// returns the identifier of the unit
    fn my_ident(&self) -> &str;

    fn to_os_write_fn_name(&self) -> String;

    fn to_os_read_fn_name(&self) -> String;

    fn base(&self) -> Option<(&str, u64)> {
        None
    }

    fn to_struct_name(&self, unit: U) -> String {
        format!("{}_{}", unit.to_struct_name(), self.my_ident())
    }

    fn to_type_name(&self, unit: U) -> String {
        let mut s = self.to_struct_name(unit);
        s.push_str("__t");
        s
    }

    fn to_ctype(&self, unit: U) -> C::Type {
        C::Type::new_typedef(&self.to_type_name(unit))
    }

    fn to_mask_name(&self, unit: U) -> String {
        format!(
            "{}_{}__MASK",
            unit.my_ident().to_uppercase(),
            self.my_ident().to_uppercase()
        )
    }

    fn to_wr_fn(&self, unit: U) -> String {
        field_wr_fn_name_str(unit.my_ident(), self.my_ident())
    }

    fn to_wr_fn_call(&self, unit: U, unit_var: C::Expr, val: C::Expr) -> C::Expr {
        let fname = self.to_wr_fn(unit);
        C::Expr::fn_call(&fname, vec![unit_var, val])
    }

    fn to_rd_fn(&self, unit: U) -> String {
        field_rd_fn_name_str(unit.my_ident(), self.my_ident())
    }

    fn to_rd_fn_call(&self, unit: U, unit_var: C::Expr) -> C::Expr {
        let fname = self.to_rd_fn(unit);
        C::Expr::fn_call(&fname, vec![unit_var])
    }

    fn to_get_val_fn(&self, unit: U) -> String {
        field_get_raw_fn_name_str(unit.my_ident(), self.my_ident())
    }

    /// obtains the raw value from the field struct
    fn to_get_val_fn_call(&self, unit: U, val: C::Expr) -> C::Expr {
        let fname = self.to_get_val_fn(unit);
        C::Expr::fn_call(&fname, vec![val])
    }

    fn to_set_val_fn(&self, unit: U) -> String {
        field_set_raw_fn_name_str(unit.my_ident(), self.my_ident())
    }

    /// calls the initializer for the field struct with the raw value
    fn to_set_val_fn_call(&self, unit: U, val: C::Expr) -> C::Expr {
        let fname = self.to_set_val_fn(unit);
        C::Expr::fn_call(&fname, vec![val])
    }

    fn to_os_wr_fn(&self, _unit: U, unit_var: &C::Expr, val: &C::Expr) -> C::Expr {
        let fname = self.to_os_write_fn_name();
        let mut args = Vec::new();
        if let Some((base, offset)) = self.base() {
            args.push(C::Expr::field_access(unit_var, base));
            args.push(C::Expr::new_num(offset))
        }
        args.push(val.clone());

        C::Expr::fn_call(&fname, args)
    }

    fn to_os_rd_fn(&self, _unit: U, unit_var: &C::Expr) -> C::Expr {
        let fname = self.to_os_read_fn_name();
        let mut args = Vec::new();
        if let Some((base, offset)) = self.base() {
            args.push(C::Expr::field_access(unit_var, base));
            args.push(C::Expr::new_num(offset))
        }
        C::Expr::fn_call(&fname, args)
    }
}

impl<U> FieldUtils<U> for &VelosiAstInterfaceField
where
    U: UnitUtils,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }

    fn base(&self) -> Option<(&str, u64)> {
        match self {
            VelosiAstInterfaceField::Memory(mem) => Some((mem.ident().as_str(), mem.offset)),
            VelosiAstInterfaceField::Register(_reg) => None,
            VelosiAstInterfaceField::Mmio(mmio) => Some((mmio.ident().as_str(), mmio.offset)),
        }
    }

    fn to_os_write_fn_name(&self) -> String {
        match self {
            VelosiAstInterfaceField::Memory(mem) => os_memory_write_fn_name(mem),
            VelosiAstInterfaceField::Register(reg) => os_register_write_fn_name(reg),
            VelosiAstInterfaceField::Mmio(mmio) => os_mmio_write_fn_name(mmio),
        }
    }

    fn to_os_read_fn_name(&self) -> String {
        match self {
            VelosiAstInterfaceField::Memory(mem) => os_memory_read_fn_name(mem),
            VelosiAstInterfaceField::Register(reg) => os_register_read_fn_name(reg),
            VelosiAstInterfaceField::Mmio(mmio) => os_mmio_read_fn_name(mmio),
        }
    }
}

impl<U> FieldUtils<U> for &VelosiAstInterfaceRegisterField
where
    U: UnitUtils,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }

    fn to_os_write_fn_name(&self) -> String {
        os_register_write_fn_name(self)
    }

    fn to_os_read_fn_name(&self) -> String {
        os_register_read_fn_name(self)
    }
}

impl<U> FieldUtils<U> for &dyn VelosiAstField
where
    U: UnitUtils,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }

    fn base(&self) -> Option<(&str, u64)> {
        if let Some(field) = self.as_any().downcast_ref::<VelosiAstInterfaceField>() {
            match field {
                VelosiAstInterfaceField::Memory(mem) => Some((mem.ident().as_str(), mem.offset)),
                VelosiAstInterfaceField::Register(_reg) => None,
                VelosiAstInterfaceField::Mmio(mmio) => Some((mmio.ident().as_str(), mmio.offset)),
            }
        } else {
            None
        }
    }

    fn to_os_write_fn_name(&self) -> String {
        if let Some(field) = self.as_any().downcast_ref::<VelosiAstInterfaceField>() {
            match field {
                VelosiAstInterfaceField::Memory(mem) => os_memory_write_fn_name(mem),
                VelosiAstInterfaceField::Register(reg) => os_register_write_fn_name(reg),
                VelosiAstInterfaceField::Mmio(mmio) => os_mmio_write_fn_name(mmio),
            }
        } else {
            unreachable!();
        }
    }

    fn to_os_read_fn_name(&self) -> String {
        if let Some(field) = self.as_any().downcast_ref::<VelosiAstInterfaceField>() {
            match field {
                VelosiAstInterfaceField::Memory(mem) => os_memory_read_fn_name(mem),
                VelosiAstInterfaceField::Register(reg) => os_register_read_fn_name(reg),
                VelosiAstInterfaceField::Mmio(mmio) => os_mmio_read_fn_name(mmio),
            }
        } else {
            unreachable!();
        }
    }
}

impl<U> FieldUtils<U> for &VelosiAstInterfaceMemoryField
where
    U: UnitUtils,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }

    fn base(&self) -> Option<(&str, u64)> {
        Some((self.ident().as_str(), self.offset))
    }

    fn to_os_write_fn_name(&self) -> String {
        os_memory_write_fn_name(self)
    }

    fn to_os_read_fn_name(&self) -> String {
        os_memory_read_fn_name(self)
    }
}

impl<U> FieldUtils<U> for &VelosiAstInterfaceMmioField
where
    U: UnitUtils,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }

    fn base(&self) -> Option<(&str, u64)> {
        Some((self.ident().as_str(), self.offset))
    }

    fn to_os_write_fn_name(&self) -> String {
        os_mmio_write_fn_name(self)
    }

    fn to_os_read_fn_name(&self) -> String {
        os_mmio_write_fn_name(self)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface Field Slice Utils
////////////////////////////////////////////////////////////////////////////////////////////////////

pub fn slice_wr_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!(
        "{}_{}_{}__wr",
        unit.to_lowercase(),
        field.to_lowercase(),
        slice.to_lowercase()
    )
}

pub fn slice_rd_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!(
        "{}_{}_{}__rd",
        unit.to_lowercase(),
        field.to_lowercase(),
        slice.to_lowercase()
    )
}

pub fn slice_insert_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!(
        "{}_{}_{}__insert",
        unit.to_lowercase(),
        field.to_lowercase(),
        slice.to_lowercase()
    )
}

pub fn slice_extract_fn_name_str(unit: &str, field: &str, slice: &str) -> String {
    format!(
        "{}_{}_{}__extract",
        unit.to_lowercase(),
        field.to_lowercase(),
        slice.to_lowercase()
    )
}

pub trait SliceUtils<U, F>
where
    U: UnitUtils,
    F: FieldUtils<U>,
{
    fn my_ident(&self) -> &str;

    fn to_wr_fn(&self, unit: U, field: F) -> String {
        slice_wr_fn_name_str(unit.my_ident(), field.my_ident(), self.my_ident())
    }

    fn to_rd_fn(&self, unit: U, field: F) -> String {
        slice_rd_fn_name_str(unit.my_ident(), field.my_ident(), self.my_ident())
    }

    fn to_insert_fn(&self, unit: U, field: F) -> String {
        slice_insert_fn_name_str(unit.my_ident(), field.my_ident(), self.my_ident())
    }

    fn to_insert_fn_call(
        &self,
        unit: U,
        field: F,
        field_var: C::Expr,
        val_var: C::Expr,
    ) -> C::Expr {
        let insert_fn = self.to_insert_fn(unit, field);
        C::Expr::fn_call(&insert_fn, vec![field_var, val_var])
    }

    fn to_extract_fn(&self, unit: U, field: F) -> String {
        slice_extract_fn_name_str(unit.my_ident(), field.my_ident(), self.my_ident())
    }

    fn to_extract_fn_call(&self, unit: U, field: F, field_var: C::Expr) -> C::Expr {
        let extract_fn = self.to_extract_fn(unit, field);
        C::Expr::fn_call(&extract_fn, vec![field_var])
    }
}

impl<U, F> SliceUtils<U, F> for &VelosiAstFieldSlice
where
    U: UnitUtils,
    F: FieldUtils<U>,
{
    fn my_ident(&self) -> &str {
        self.ident()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// OS Support Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn os_mmio_read_fn_name(field: &VelosiAstInterfaceMmioField) -> String {
    format!("os_mmio_read_{}", field.nbits())
}

fn os_mmio_write_fn_name(field: &VelosiAstInterfaceMmioField) -> String {
    format!("os_mmio_write_{}", field.nbits())
}

fn os_register_read_fn_name(field: &VelosiAstInterfaceRegisterField) -> String {
    format!("os_register_read_{}", field.ident())
}

fn os_register_write_fn_name(field: &VelosiAstInterfaceRegisterField) -> String {
    format!("os_register_write_{}", field.ident())
}

fn os_memory_read_fn_name(field: &VelosiAstInterfaceMemoryField) -> String {
    format!("os_memory_read_{}", field.nbits())
}

fn os_memory_write_fn_name(field: &VelosiAstInterfaceMemoryField) -> String {
    format!("os_memory_write_{}", field.nbits())
}

// pub fn os_register_write_fn(
//     _unit_var: &C::Expr,
//     field: &VelosiAstInterfaceRegisterField,
//     val: &C::Expr,
// ) -> C::Expr {
//     let fnname = format!("os_register_write_{}", field.nbits());

//     C::Expr::fn_call(&fnname, vec![val.clone()])
// }

// pub fn os_register_read_fn(
//     _unit_var: &C::Expr,
//     field: &VelosiAstInterfaceRegisterField,
// ) -> C::Expr {
//     let fnname = format!("os_register_read_{}", field.nbits());

//     C::Expr::fn_call(&fnname, vec![])
// }

// pub fn os_memory_write_fn(
//     unit_var: &C::Expr,
//     field: &VelosiAstInterfaceMemoryField,
//     val: &C::Expr,
// ) -> C::Expr {
//     let fnname = format!("os_memory_write_{}", field.nbits());
//     let base = format!("_{}", field.base.as_str());

//     C::Expr::fn_call(
//         &fnname,
//         vec![
//             C::Expr::field_access(unit_var, &base),
//             C::Expr::new_num(field.offset),
//             val.clone(),
//         ],
//     )
// }

// pub fn os_memory_read_fn(unit_var: &C::Expr, field: &VelosiAstInterfaceMemoryField) -> C::Expr {
//     let fnname = format!("os_memory_read_{}", field.nbits());
//     let base = format!("_{}", field.base);

//     C::Expr::fn_call(
//         &fnname,
//         vec![
//             C::Expr::field_access(unit_var, &base),
//             C::Expr::new_num(field.offset),
//         ],
//     )
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Others
////////////////////////////////////////////////////////////////////////////////////////////////////

/// creates a strng reprsenting the mask value
pub fn to_mask_str(m: u64, len: u64) -> String {
    match len {
        0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
        9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
        17..=32 => format!("0x{:08x}U", (m & 0xffffffff) as u32),
        33..=64 => format!("0x{m:016x}ULL"),
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
        m.set_value(&format!("(uint64_t)({})", c.value));
    } else {
        m.set_value(&format!("{}", c.value));
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
            let fname = slice_insert_fn_name_str(unit, field, slice);
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
            let fname = slice_extract_fn_name_str(unit, field, slice);
            c.fn_call(&fname, vec![]);
        }
        VelosiOperation::WriteAction(field) => {
            let fname = field_wr_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field.as_str()).unwrap();
            c.fn_call(&fname, vec![u.clone(), f.clone()]);
        }
        VelosiOperation::ReadAction(field) => {
            let fname = field_rd_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field.as_str()).unwrap();
            c.assign(f.clone(), C::Expr::fn_call(&fname, vec![u.clone()]));
        }
        VelosiOperation::Return => (),
    }
}

pub fn expr_to_cpp(unit: &VelosiAstUnitSegment, expr: &VelosiAstExpr) -> C::Expr {
    use VelosiAstExpr::*;
    match expr {
        IdentLiteral(i) => {
            C::Expr::new_var(i.ident().as_str(), unit.ptype_to_ctype(expr.result_type()))
        }
        NumLiteral(i) => C::Expr::new_num(i.val),
        BoolLiteral(i) => {
            if i.val {
                C::Expr::btrue()
            } else {
                C::Expr::bfalse()
            }
        }
        BinOp(i) => match i.op {
            VelosiAstBinOp::LShift => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "<<", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::RShift => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), ">>", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::And => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "&", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Or => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "|", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Xor => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "^", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Plus => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "+", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Minus => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "-", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Multiply => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "*", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Divide => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "/", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Modulo => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "%", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Eq => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "==", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Ne => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "!=", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Lt => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "<", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Gt => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), ">", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Le => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "<=", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Ge => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), ">=", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Land => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "&&", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Lor => {
                C::Expr::binop(expr_to_cpp(unit, &i.lhs), "||", expr_to_cpp(unit, &i.rhs))
            }
            VelosiAstBinOp::Implies => C::Expr::binop(
                C::Expr::uop("!", expr_to_cpp(unit, &i.lhs)),
                "||",
                expr_to_cpp(unit, &i.rhs),
            ),
        },
        UnOp(i) => match i.op {
            VelosiAstUnOp::Not => C::Expr::uop("~", expr_to_cpp(unit, &i.expr)),
            VelosiAstUnOp::LNot => C::Expr::uop("!", expr_to_cpp(unit, &i.expr)),
        },
        Quantifier(_i) => panic!("don't know how to handle quantifier"),
        FnCall(_i) => panic!("don't know how to handle fncalls"),
        IfElse(_i) => panic!("don't know how to handle ifelse"),
        Slice(_i) => panic!("don't know how to handle slices"),
        Range(_i) => panic!("don't know how to handle range"),
    }
}
