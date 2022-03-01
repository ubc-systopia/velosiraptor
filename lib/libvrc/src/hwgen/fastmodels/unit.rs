// Velosiraptor Compiler
//
//
// MIT License
//
// Copyright (c) 2022 The University of British Columbia, Vancouver, BC, Canada
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

//! # The FastModels Platform Generator: State
//!
//! This module generates the unit description of the Arm FastModels implementation
//! of the translation unit.

// the path buffer
use std::path::Path;

// other libraries
use crustal as C;

// the defined errors
use crate::ast::{Expr, Method, Stmt, Type, Unit};
use crate::hwgen::fastmodels::add_header;
use crate::hwgen::fastmodels::interface::{interface_class_name, interface_header_file};
use crate::hwgen::fastmodels::state::{state_class_name, state_header_file};
use crate::hwgen::HWGenError;

/// generates the name of the state field header file
pub fn unit_header_file(name: &str) -> String {
    format!("{}_unit.hpp", name)
}

/// generates the path of the state field header file
pub fn unit_header_file_path(name: &str) -> String {
    format!("include/{}", unit_header_file(name))
}

/// generates the name of the state field header file
pub fn unit_impl_file(name: &str) -> String {
    format!("{}_unit.cpp", name)
}

/// generates the name of the state class
pub fn unit_class_name(name: &str) -> String {
    format!("{}{}Unit", name[0..1].to_uppercase(), &name[1..])
}

fn add_constructor(c: &mut C::Class, ifn: &str, scn: &str) {
    // TranslationUnit::TranslationUnit(std::string const                     &name,
    //                                  pv::RandomContextTransactionGenerator *ptw_pvbus)
    //     : TranslationUnitBase(name, ptw_pvbus, 0, CONFIG_END_ADDRESS)
    //     , _state(TranslationUnitState())
    //     , _interface(TranslationUnitInterface(&_state))
    // {
    // }
    //     TranslationUnit(std::string const                     &name,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus = nullptr);
    let mut arg0_type = C::Type::new_std_string();
    arg0_type.constant().reference();

    let mut arg1_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg1_type.pointer();

    c.new_constructor()
        .private()
        .push_param(C::MethodParam::new("name", arg0_type.clone()))
        .push_parent_initializer(C::Expr::fn_call(
            "TranslationUnitBase",
            vec![
                C::Expr::new_var("name", arg0_type),
                C::Expr::new_var("ptw_pvbus", arg1_type.clone()),
            ],
        ))
        .push_initializer("_state", C::Expr::fn_call(scn, vec![]))
        .push_initializer(
            "_interface",
            C::Expr::fn_call(
                ifn,
                vec![C::Expr::addr_of(&C::Expr::new_var(
                    "_state",
                    C::Type::new_class("Interface"),
                ))],
            ),
        )
        .new_param("ptw_pvbus", arg1_type)
        .set_default_value("nullptr");
}

fn add_create(c: &mut C::Class, ucn: &str) {
    // static TranslationUnit *create(sg::ComponentBase *parentComponent, std::string const &name,
    //     sg::CADIBase                          *cadi,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus);
    // TODO: finish

    let unit_ptr_type = C::Type::to_ptr(&C::Type::new_class(ucn));

    let m = c
        .new_method("create", unit_ptr_type.clone())
        .set_public()
        .set_static();

    let mut arg0_type = C::Type::new_class("sg::ComponentBase");
    arg0_type.pointer();

    let mut arg1_type = C::Type::new_std_string();
    arg1_type.constant().reference();

    let mut arg2_type = C::Type::new_class("sg::CADIBase ");
    arg2_type.pointer();

    let mut arg3_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg3_type.pointer();

    // arguments
    m.push_param(C::MethodParam::new("parentComponent", arg0_type))
        .push_param(C::MethodParam::new("name", arg1_type))
        .push_param(C::MethodParam::new("cadi", arg2_type))
        .push_param(C::MethodParam::new("ptw_pvbus", arg3_type));

    let unitvar = C::Expr::new_var("t", unit_ptr_type.clone());

    let statevar = C::Expr::field_access(&unitvar, "_state");
    let ifvar = C::Expr::field_access(&unitvar, "_interface");

    //  TranslationUnit *t;
    m.body()
        .variable(C::Variable::new("t", unit_ptr_type))
        .fn_call(
            "Logging::debug",
            vec![C::Expr::new_str("Register::do_read()")],
        )
        // t = new TranslationUnit(name, ptw_pvbus)
        .assign(
            unitvar.clone(),
            C::Expr::Raw(format!(" new {}(name, ptw_pvbus)", ucn)),
        )
        // t->_state.print_state_fields();
        .method_call(statevar, "print_state_fields", vec![])
        // t->_interface.debug_print_interface();
        .method_call(ifvar, "debug_print_interface", vec![])
        // return t;
        .return_expr(unitvar);

    // TranslationUnit *TranslationUnit::create(sg::ComponentBase *parentComponent,
    //                                          std::string const &name, sg::CADIBase *cadi,
    //                                          pv::RandomContextTransactionGenerator *ptw_pvbus)
    // {
    //     Logging::debug("creating new translation unit.\n");

    //     TranslationUnit *t = new TranslationUnit(name, ptw_pvbus);

    //     t->_interface.debug_print_interface();

    //     Logging::debug("translation unit created.\n");

    //     return t;
    // }
}

fn state_field_access(path: &[String]) -> C::Expr {
    let st = C::Expr::field_access(&C::Expr::this(), "_state");

    if path.len() == 1 {
        let accname = format!("get_{}_val", &path[0]);
        return C::Expr::method_call(&st, &accname, vec![]);
    }

    if path.len() == 2 {
        let accname = format!("{}_field", &path[0]);
        let mut fld = C::Expr::method_call(&st, &accname, vec![]);
        // we'll get back a pointer
        fld.set_ptr();
        let accname = format!("get_{}_val", &path[1]);
        return C::Expr::method_call(&fld, &accname, vec![]);
    }

    panic!("unhandled!")
}

fn expr_to_cpp(expr: &Expr) -> C::Expr {
    use Expr::*;
    match expr {
        Identifier { path, .. } => {
            match path[0].as_str() {
                "state" => {
                    // this->_state.control_field()
                    state_field_access(&path[1..])
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
            let e = expr_to_cpp(lhs);
            let e2 = expr_to_cpp(rhs);
            C::Expr::binop(e, &o, e2)
        }
        UnaryOperation { op, val, .. } => {
            let o = format!("{}", op);
            let e = expr_to_cpp(val);
            C::Expr::uop(&o, e)
        }
        FnCall { path, args, .. } => {
            if path.len() != 1 {
                panic!("TODO: handle multiple path components");
            }
            C::Expr::method_call(
                &C::Expr::this(),
                &path[0],
                args.iter().map(expr_to_cpp).collect(),
            )
        }
        Slice { .. } => panic!("don't know how to handle slice"),
        Element { .. } => panic!("don't know how to handle element"),
        Range { .. } => panic!("don't know how to handle range"),
        Quantifier { .. } => panic!("don't know how to handle quantifier"),
    }
}

fn assert_to_cpp(expr: &Expr) -> C::IfElse {
    let mut c = C::IfElse::with_expr(expr_to_cpp(expr));
    c.then_branch()
        .raw(format!(
            "Logging::debug(\"TranslationUnit::translate() precondition/assertion failed ({})\");",
            expr
        ))
        .return_expr(C::Expr::bfalse());
    c
}

fn handle_requires_assert(method: &mut C::Method, expr: &Expr) {
    method.body().ifelse(assert_to_cpp(expr));
}

fn stmt_to_cpp(s: &Stmt) -> C::Block {
    use Stmt::*;
    match s {
        Block { stmts, .. } => stmts.iter().fold(C::Block::new(), |mut acc, x| {
            acc.merge(stmt_to_cpp(x));
            acc
        }),
        Return { expr, .. } => {
            let mut b = C::Block::new();
            b.return_expr(expr_to_cpp(expr));
            b
        }
        Let {
            typeinfo: _,
            lhs: _,
            rhs: _,
            pos: _,
        } => panic!("not handled yet!"),
        Assert { expr, pos: _ } => {
            let mut b = C::Block::new();
            b.ifelse(assert_to_cpp(expr));
            b
        }
        IfElse {
            cond,
            then,
            other,
            pos: _,
        } => {
            let mut b = C::Block::new();
            let mut ifelse = C::IfElse::with_expr(expr_to_cpp(cond));
            if let Some(other) = other.as_ref() {
                ifelse.set_other(stmt_to_cpp(other));
            }
            ifelse.set_then(stmt_to_cpp(then));
            b.ifelse(ifelse);
            b
        }
    }
}

fn add_translate(c: &mut C::Class, tm: &Method) {
    // virtual bool do_translate(lvaddr_t src_addr, size_t size, access_mode_t mode,
    // lpaddr_t *dst_addr) set_overridee;

    let src_addr_param = C::MethodParam::new(&tm.args[0].name, C::Type::new_typedef("lvaddr_t"));
    let size_param = C::MethodParam::new("size", C::Type::new_size());
    let mode_param = C::MethodParam::new(&tm.args[1].name, C::Type::new_typedef("access_mode_t"));
    let dst_addr_param = C::MethodParam::new(
        "dst_addr",
        C::Type::to_ptr(&C::Type::new_typedef("lpaddr_t")),
    );
    let m = c
        .new_method("do_translate", C::Type::new_bool())
        .set_public()
        .set_virtual()
        .set_override()
        .push_param(src_addr_param)
        .push_param(size_param)
        .push_param(mode_param)
        .push_param(dst_addr_param);

    for e in &tm.requires {
        handle_requires_assert(m, e);
    }

    if let Some(body) = &tm.stmts {
        m.set_body(stmt_to_cpp(body));
    }
}

fn ast_type_to_c_type(t: &Type) -> C::Type {
    match t {
        Type::Boolean => C::Type::new_bool(),
        Type::Integer => C::Type::new_uint(64),
        Type::Size => C::Type::new_size(),
        Type::Address => C::Type::new_typedef("genaddr_t"),
        _ => panic!("unhandled!"),
    }
}

fn add_method(c: &mut C::Class, tm: &Method) {
    match &tm.name[..] {
        "translate" => add_translate(c, tm),
        "map" => return,
        "unmap" => return,
        "protect" => return,
        _ => (),
    }

    let m = c.new_method(&tm.name, ast_type_to_c_type(&tm.rettype));
    for p in &tm.args {
        m.push_param(C::MethodParam::new(&p.name, ast_type_to_c_type(&p.ptype)));
    }

    for e in &tm.requires {
        handle_requires_assert(m, e);
    }

    if let Some(body) = &tm.stmts {
        m.set_body(stmt_to_cpp(body));
    }
}

pub fn generate_unit_header(name: &str, unit: &Unit, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, name, "unit");

    let ifn = interface_class_name(name);
    let scn = state_class_name(name);
    let ucn = unit_class_name(name);

    // set the header guard, and create
    let hdrguard = format!("{}_UNIT_HPP_", name.to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // adding the includes
    s.new_comment("system includes");
    s.new_include("string.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("generic/types.hpp", true);
    s.new_include("generic/translation_unit_base.hpp", true);

    s.new_comment("translation unit specific includes");
    let statehdr = state_header_file(name);
    s.new_include(&statehdr, true);
    let ifhdr = interface_header_file(name);
    s.new_include(&ifhdr, true);

    // create a new class in the scope
    let c = s.new_class(&ucn);

    c.set_base("TranslationUnitBase", C::Visibility::Public);

    add_constructor(c, &ifn, &scn);
    add_create(c, &ucn);

    //
    // virtual UnitBase *get_interface(void) set_overridee
    // {
    //     return &this->_interface;
    // }
    c.new_method(
        "get_interface",
        C::Type::to_ptr(&C::Type::new_class("InterfaceBase")),
    )
    .set_public()
    .set_virtual()
    .set_inside_def()
    .set_override()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "_interface",
    )));

    //
    // virtual StateBase *get_state(void) set_overridee
    // {
    //     return &this->_state;
    // }
    c.new_method(
        "get_state",
        C::Type::to_ptr(&C::Type::new_class("StateBase")),
    )
    .set_public()
    .set_virtual()
    .set_override()
    .set_inside_def()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "_state",
    )));

    // attributes

    let state_ptr_type = C::Type::new_class(&scn);
    let iface_ptr_type = C::Type::new_class(&ifn);

    // add the state attribute
    c.new_attribute("_state", state_ptr_type);
    c.new_attribute("_interface", iface_ptr_type);

    // TODO: handle the methods!
    for m in &unit.methods {
        add_method(c, m);
    }

    // save the scope
    let filename = unit_header_file_path(name);
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_unit_impl(name: &str, unit: &Unit, outdir: &Path) -> Result<(), HWGenError> {
    let mut scope = C::Scope::new();

    // add the header
    add_header(&mut scope, name, "unit");

    scope.new_comment("system includes");
    scope.new_include("string.h", true);
    scope.new_include("assert.h", true);

    scope.new_comment("framework includes");
    scope.new_include("generic/types.hpp", true);
    scope.new_include("generic/logging.hpp", true);

    scope.new_comment("translation unit specific includes");
    let unithdr = unit_header_file(name);
    scope.new_include(&unithdr, true);

    // create a new class in the scope
    let ucn = unit_class_name(name);
    let c = scope.new_class(ucn.as_str());

    c.set_base("TranslationUnitBase", C::Visibility::Public);

    let ifn = interface_class_name(name);
    let scn = state_class_name(name);

    add_constructor(c, &ifn, &scn);
    add_create(c, &ucn);

    /*
     * -------------------------------------------------------------------------------------------
     * Translations
     * -------------------------------------------------------------------------------------------
     */

    // TODO: handle the methods!
    for m in &unit.methods {
        add_method(c, m)
    }

    let filename = unit_impl_file(name);
    scope.set_filename(&filename);

    scope.to_file(outdir, false)?;

    Ok(())
}
