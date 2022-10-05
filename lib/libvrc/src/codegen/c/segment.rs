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

//! Segment Generation (C)

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crustal as C;

use super::utils;
use crate::ast::{AstNodeGeneric, Expr, Segment, Stmt, Type};
use crate::codegen::CodeGenError;
use crate::synth::{OpExpr, Operation};

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &Segment) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in &unit.consts {
        utils::add_const_def(scope, c);
    }
}

fn add_unit_flags(scope: &mut C::Scope, unit: &Segment) {
    let structname = format!("{}_flags", unit.name);
    if let Some(flags) = &unit.flags {
        scope.new_comment("Defined unit flags");

        let st = scope.new_struct(&structname);

        for flag in &flags.flags {
            let f = st.new_field(flag.name(), C::Type::new_uint64());
            f.set_bitfield_width(1);
        }
    } else {
        scope.new_comment("Unit has no defined flags");
        scope.new_struct(&structname);
    }
    let tyname = format!("{}_t", structname);
    scope.new_typedef(&tyname, C::Type::new_struct(&structname));
}

// /// adds the struct definition of the unit to the scope
// fn add_struct_definition(scope: &mut C::Scope, unit: &Unit) {
//     // a field is a struct
//     //
//     // field_name  --> struct FieldName {  val: u64 };

//     // create the struct in the scope
//     let st = scope.new_struct(unit.name());

//     // make it public
//     st.vis("pub");

//     // add the doc field to the struct
//     st.doc(&format!(
//         "Represents the Unit type '{}'.\n@loc: {}",
//         unit.name(),
//         unit.location()
//     ));

//     // it has a single field, called 'val'
//     //st.field("val", to_rust_type(field.nbits()));
// }

fn add_constructor_function(scope: &mut C::Scope, unit: &Segment) {
    let fname = utils::constructor_fn_name(unit.name());

    let unittype = C::Type::new_typedef(&utils::unit_type_name(unit.name()));

    let mut fun = C::Function::with_string(fname, unittype);
    fun.set_static().set_inline();

    let mut params = Vec::new();
    for p in &unit.params {
        let param = fun.new_param(p.name(), C::Type::new_uint64()).to_expr();
        params.push((&p.name, param));
    }

    let body = fun.body();

    let unittype = C::Type::new_typedef(&utils::unit_type_name(&unit.name));
    let tunit = body.new_variable("targetunit", unittype).to_expr();

    for (name, p) in params {
        let n = utils::unit_struct_field_name(name);
        body.assign(C::Expr::field_access(&tunit, &n), p);
    }

    body.return_expr(tunit);

    scope.push_function(fun);
}

fn state_field_access(unit: &str, path: &[String]) -> C::Expr {
    let unit_var = C::Expr::new_var("unit", C::Type::new_void());
    if path.len() == 1 {
        let fname = utils::if_field_rd_fn_name_str(unit, &path[0]);
        return C::Expr::fn_call(&fname, vec![unit_var]);
    }

    if path.len() == 2 {
        let fname = utils::if_field_rd_slice_fn_name_str(unit, &path[0], &path[1]);
        return C::Expr::fn_call(&fname, vec![unit_var]);
    }

    panic!("unhandled!")
}

fn expr_to_cpp(unit: &str, expr: &Expr) -> C::Expr {
    use Expr::*;
    match expr {
        Identifier { path, .. } => {
            match path[0].as_str() {
                "state" => {
                    // this->_state.control_field()
                    state_field_access(unit, &path[1..])
                }
                "interface" => panic!("state not implemented"),
                p => C::Expr::new_var(p, C::Type::new_int(64)),
            }
        }
        Number { value, .. } => C::Expr::new_num(*value),
        Boolean { value: true, .. } => C::Expr::btrue(),
        Boolean { value: false, .. } => C::Expr::bfalse(),
        BinaryOperation { op, lhs, rhs, .. } => {
            let o = format!("{}", op);
            let e = expr_to_cpp(unit, lhs);
            let e2 = expr_to_cpp(unit, rhs);
            C::Expr::binop(e, &o, e2)
        }
        UnaryOperation { op, val, .. } => {
            let o = format!("{}", op);
            let e = expr_to_cpp(unit, val);
            C::Expr::uop(&o, e)
        }
        FnCall { path, args, .. } => {
            if path.len() != 1 {
                panic!("TODO: handle multiple path components");
            }
            C::Expr::method_call(
                &C::Expr::this(),
                &path[0],
                args.iter().map(|x| expr_to_cpp(unit, x)).collect(),
            )
        }
        Slice { .. } => panic!("don't know how to handle slice"),
        Element { .. } => panic!("don't know how to handle element"),
        Range { .. } => panic!("don't know how to handle range"),
        Quantifier { .. } => panic!("don't know how to handle quantifier"),
    }
}

fn stmt_to_cpp(unit: &str, s: &Stmt) -> C::Block {
    use Stmt::*;
    match s {
        Block { stmts, .. } => stmts.iter().fold(C::Block::new(), |mut acc, x| {
            acc.merge(stmt_to_cpp(unit, x));
            acc
        }),
        Return { expr, .. } => {
            let mut b = C::Block::new();

            let t = C::Type::new_uint64().to_ptr();
            let v = C::Expr::new_var("pa", t);
            b.assign(C::Expr::deref(&v), expr_to_cpp(unit, expr));
            b.return_expr(C::Expr::btrue());
            b
        }
        Let { .. } => panic!("not handled yet!"),
        Assert { .. } => panic!("not handled yet!"),
        IfElse {
            cond,
            then,
            other,
            pos: _,
        } => {
            let mut b = C::Block::new();
            let mut ifelse = C::IfElse::with_expr(expr_to_cpp(unit, cond));
            if let Some(other) = other.as_ref() {
                ifelse.set_other(stmt_to_cpp(unit, other));
            }
            ifelse.set_then(stmt_to_cpp(unit, then));
            b.ifelse(ifelse);
            b
        }
    }
}

fn add_translate_function(scope: &mut C::Scope, unit: &Segment) {
    let fname = utils::translate_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    fun.new_param("pa", C::Type::new_uint64().to_ptr());

    if !unit.state().is_memory() {
        fun.body().return_expr(C::Expr::bfalse());
        scope.push_function(fun);
        return;
    }

    if let Some(f) = unit.get_method("translate") {
        let body = fun.body();

        for c in &f.requires {
            body.new_ifelse(&C::Expr::not(expr_to_cpp(unit.name(), c)))
                .then_branch()
                .new_return(Some(&C::Expr::bfalse()));
        }

        if let Some(stmt) = &f.stmts {
            body.merge(stmt_to_cpp(unit.name(), stmt));
        }
    } else {
        fun.body().new_comment("there was no translate method");
    }

    // if !(va < 4096) || state.pte.present != 1 {
    //    return false;
    // }
    // *pa = va + (state.pte.base << 12);
    // return true;

    // fun.new_param("size", C::Type::new_size());
    // fun.new_param("pa", C::Type::new_uint64());
    // fun.new_param("flags", C::Type::new_int(64));

    scope.push_function(fun);
}

fn oparg_to_rust_expr(op: &OpExpr) -> Option<C::Expr> {
    match op {
        OpExpr::None => None,
        OpExpr::Num(x) => Some(C::Expr::new_num(*x)),
        OpExpr::Var(x) => Some(C::Expr::new_var(x, C::Type::new_int(64))),
        OpExpr::Shl(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "<<",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Shr(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            ">>",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::And(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "&",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Or(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "|",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Add(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "+",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Sub(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "-",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Mul(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "*",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Div(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "/",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Mod(x, y) => Some(C::Expr::binop(
            oparg_to_rust_expr(x).unwrap(),
            "%",
            oparg_to_rust_expr(y).unwrap(),
        )),
        OpExpr::Not(x) => Some(C::Expr::uop("!", oparg_to_rust_expr(x).unwrap())),
        OpExpr::Flags(v, f) => Some(C::Expr::field_access(
            &C::Expr::new_var(&v, C::Type::new_typedef("dummy")),
            &f,
        )),
    }
}

fn op_to_rust_expr(unit: &str, c: &mut C::Block, op: &Operation, vars: &HashMap<String, C::Expr>) {
    match op {
        Operation::Insert {
            field,
            slice: Some(slice),
            arg,
        } => {
            let fname = utils::field_slice_insert_fn_name_str(unit, field, slice);
            //format!("v_{}.insert_{}({});", field, slice, oparg_to_rust_expr(arg))
            let v = vars.get(field).unwrap();
            let mut args = vec![v.clone()];
            if let Some(a) = oparg_to_rust_expr(arg) {
                args.push(a);
            }
            c.assign(v.clone(), C::Expr::fn_call(&fname, args));
        }
        Operation::Insert {
            field,
            slice: None,
            arg,
        } => {
            let fname = utils::field_set_raw_fn_name_str(unit, field);
            let v = vars.get(field).unwrap();
            let mut args = Vec::new();
            if let Some(a) = oparg_to_rust_expr(arg) {
                args.push(a);
            }
            c.assign(v.clone(), C::Expr::fn_call(&fname, args));
        }
        Operation::Extract {
            field,
            slice: Some(slice),
        } => {
            let fname = utils::field_slice_extract_fn_name_str(unit, field, slice);
            c.fn_call(&fname, vec![]);
        }
        Operation::Extract { field, slice: None } => {
            let fname = utils::field_get_raw_fn_name_str(unit, field);
            c.fn_call(&fname, vec![]);
        }
        Operation::WriteAction { field } => {
            let fname = utils::if_field_wr_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field).unwrap();
            c.fn_call(&fname, vec![u.clone(), f.clone()]);
        }
        Operation::ReadAction { field } => {
            let fname = utils::if_field_rd_fn_name_str(unit, field);
            let u = vars.get("unit").unwrap();
            let f = vars.get(field).unwrap();
            c.assign(f.clone(), C::Expr::fn_call(&fname, vec![u.clone()]));
        }
        Operation::Return => (),
    }
}

fn ptype_to_ctype(ptype: Type, unit: &Segment) -> C::Type {
    match ptype {
        Type::VirtualAddress => C::Type::new_typedef("vaddr_t"),
        Type::PhysicalAddress => C::Type::new_typedef("paddr_t"),
        Type::Size => C::Type::new_typedef("size_t"),
        Type::Flags => C::Type::new_typedef(&utils::unit_flags_type(unit)),
        _ => todo!(),
    }
}

fn add_map_function(scope: &mut C::Scope, unit: &Segment) {
    let fname = utils::map_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());

    // TODO: do this with the method!

    let m_fn = unit.get_method("map").unwrap();
    for f in m_fn.args.iter() {
        fun.new_param(f.name(), ptype_to_ctype(f.ptype, unit));
    }

    // find the fields
    let mut fields = HashSet::new();
    if let Some(ops) = &unit.map_ops {
        for op in ops {
            let fname = op.fieldname();
            if fname.is_empty() {
                continue;
            }
            fields.insert(String::from(fname));
        }
    }

    fun.body().new_comment("field variables");

    for field in &fields {
        if let Some(f) = unit.interface.field_by_name(field) {
            // get the field from the unit
            let field_type = utils::field_type_name(unit, &f.field);

            let var = fun
                .body()
                .new_variable(field, C::Type::new_typedef(&field_type));

            let fncall_name = utils::field_set_raw_fn_name(unit, &f.field);
            var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
            field_vars.insert(field.clone(), var.to_expr());
        }
    }

    if let Some(ops) = &unit.map_ops {
        fun.body().new_comment("configuration sequence");
        for op in ops {
            op_to_rust_expr(unit.name(), fun.body(), op, &field_vars);
        }
    } else {
        fun.body().new_comment("there is no configuration sequence");
    }

    scope.push_function(fun);
}

fn add_unmap_function(scope: &mut C::Scope, unit: &Segment) {
    let fname = utils::unmap_fn_name(unit.name());

    let fun = scope.new_function(&fname, C::Type::new_void());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());
    fun.new_param("va", C::Type::new_uint64());
    fun.new_param("size", C::Type::new_size());

    // find the fields
    let mut fields = HashSet::new();
    if let Some(ops) = &unit.map_ops {
        for op in ops {
            let fname = op.fieldname();
            if fname.is_empty() {
                continue;
            }
            fields.insert(String::from(fname));
        }
    }

    fun.body().new_comment("field variables");

    for field in &fields {
        if let Some(f) = unit.interface.field_by_name(field) {
            // get the field from the unit
            let field_type = utils::field_type_name(unit, &f.field);

            let var = fun
                .body()
                .new_variable(field, C::Type::new_typedef(&field_type));

            let fncall_name = utils::field_set_raw_fn_name(unit, &f.field);
            var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
            field_vars.insert(field.clone(), var.to_expr());
        }
    }

    if let Some(ops) = &unit.unmap_ops {
        fun.body().new_comment("configuration sequence");
        for op in ops {
            op_to_rust_expr(unit.name(), fun.body(), op, &field_vars);
        }
    } else {
        fun.body().new_comment("there is no configuration sequence");
    }
}

fn add_protect_function(scope: &mut C::Scope, unit: &Segment) {
    let fname = utils::protect_fn_name(unit.name());

    let mut fun = C::Function::with_string(fname, C::Type::new_bool());
    fun.set_static().set_inline();

    let mut field_vars = HashMap::new();
    let unittype = C::Type::to_ptr(&C::Type::new_typedef(&utils::unit_type_name(unit.name())));

    let v = fun.new_param("unit", unittype);
    field_vars.insert(String::from("unit"), v.to_expr());

    let m_fn = unit.get_method("protect").unwrap();
    for f in m_fn.args.iter() {
        fun.new_param(f.name(), ptype_to_ctype(f.ptype, unit));
    }

    // find the fields
    let mut fields = HashSet::new();
    if let Some(ops) = &unit.map_ops {
        for op in ops {
            let fname = op.fieldname();
            if fname.is_empty() {
                continue;
            }
            fields.insert(String::from(fname));
        }
    }

    fun.body().new_comment("field variables");

    for field in &fields {
        if let Some(f) = unit.interface.field_by_name(field) {
            // get the field from the unit
            let field_type = utils::field_type_name(unit, &f.field);

            let var = fun
                .body()
                .new_variable(field, C::Type::new_typedef(&field_type));

            let fncall_name = utils::field_set_raw_fn_name(unit, &f.field);
            var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
            field_vars.insert(field.clone(), var.to_expr());
        }
    }

    if let Some(ops) = &unit.protect_ops {
        fun.body().new_comment("configuration sequence");
        for op in ops {
            op_to_rust_expr(unit.name(), fun.body(), op, &field_vars);
        }
    } else {
        fun.body().new_comment("there is no configuration sequence");
    }

    scope.push_function(fun);
}

/// generates the Segment definitions
pub fn generate(unit: &Segment, outdir: &Path) -> Result<(), CodeGenError> {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.name());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.name().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // add the header comments
    let title = format!("`{}` Unit definition ", unit.name());
    utils::add_header(s, &title);

    s.new_include("interface.h", false);

    // add the definitions
    add_unit_constants(s, unit);
    add_unit_flags(s, unit);
    add_constructor_function(s, unit);
    add_map_function(s, unit);
    add_unmap_function(s, unit);
    add_protect_function(s, unit);
    add_translate_function(s, unit);

    // save the scope
    scope.set_filename("unit.h");
    scope.to_file(outdir, true)?;

    Ok(())
}
