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

use crustal as C;
use std::path::Path;
use velosiast::ast::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
    VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIfElseExpr, VelosiAstMethod,
    VelosiAstNumLiteralExpr, VelosiAstType, VelosiAstTypeInfo, VelosiAstUnOpExpr, VelosiAstUnit,
};
use velosiast::{VelosiAstUnitEnum, VelosiAstUnitStaticMap};

use crate::fastmodels::add_header;
use crate::fastmodels::interface::{interface_class_name, interface_header_file};
use crate::fastmodels::state::{state_class_name, state_header_file};
use crate::VelosiHwGenError;

pub fn unit_header_file(name: &str) -> String {
    format!("{}_unit.hpp", name)
}

pub fn unit_impl_file(name: &str) -> String {
    format!("{}_unit.cpp", name)
}

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

fn state_field_access(access: &Vec<&str>) -> C::Expr {
    let st = C::Expr::field_access(&C::Expr::this(), "_state");

    if access.len() == 1 {
        return st;
    }

    if access.len() == 2 {
        let state_field = C::Expr::field_access(&st, access[1]);
        return C::Expr::method_call(&state_field, "get_value", vec![]);
    }

    // state.field.get_slice_value("slice");
    if access.len() == 3 {
        let state_field = C::Expr::field_access(&st, access[1]);

        return C::Expr::method_call(
            &state_field,
            "get_slice_value",
            vec![C::Expr::new_str(access[2])],
        );
    }

    panic!("unhandled!")
}

fn expr_to_cpp(expr: &VelosiAstExpr) -> C::Expr {
    use VelosiAstExpr::*;
    match expr {
        IdentLiteral(VelosiAstIdentLiteralExpr { ident, .. }) => {
            let p: Vec<&str> = ident.path_split().collect();
            match p[0] {
                "state" => {
                    // this->_state.control_field()
                    state_field_access(&p)
                }
                "interface" => panic!("state not implemented"),
                x => C::Expr::new_var(x, C::Type::new_int(64)),
            }
        }
        NumLiteral(VelosiAstNumLiteralExpr { val, .. }) => C::Expr::new_num(*val),
        BoolLiteral(VelosiAstBoolLiteralExpr { val: b, .. }) => {
            if *b {
                C::Expr::btrue()
            } else {
                C::Expr::bfalse()
            }
        }
        BinOp(VelosiAstBinOpExpr { op, lhs, rhs, .. }) => {
            let e = expr_to_cpp(lhs);
            let e2 = expr_to_cpp(rhs);
            // implies "==>" needs a special case, others should be fine in cpp
            match op {
                VelosiAstBinOp::Implies => C::Expr::binop(C::Expr::lnot(e), "||", e2),
                _ => C::Expr::binop(e, &format!("{}", op), e2),
            }
        }
        UnOp(VelosiAstUnOpExpr { op, expr, .. }) => {
            let o = format!("{}", op);
            let e = expr_to_cpp(expr);
            C::Expr::uop(&o, e)
        }
        FnCall(VelosiAstFnCallExpr { ident, args, .. }) => {
            let p: Vec<&str> = ident.path_split().collect();
            if p.len() != 1 {
                panic!("TODO: handle multiple path components");
            }
            C::Expr::method_call(
                &C::Expr::this(),
                p[0],
                args.iter().map(|a| expr_to_cpp(a.as_ref())).collect(),
            )
        }
        Slice { .. } => panic!("No C++ equivalent for expression type: slice"),
        Range { .. } => panic!("No C++ equivalent for expression type: range"),
        Quantifier { .. } => panic!("No C++ equivalent for expression type: quantifier"),
        IfElse(VelosiAstIfElseExpr {
            cond,
            then,
            other,
            loc: _,
            ..
        }) => C::Expr::ternary(expr_to_cpp(cond), expr_to_cpp(then), expr_to_cpp(other)),
    }
}

fn assert_to_cpp(expr: &VelosiAstExpr) -> C::IfElse {
    let mut c = C::IfElse::with_expr(C::Expr::lnot(expr_to_cpp(expr)));
    c.then_branch()
        .raw(format!(
            "Logging::debug(\"TranslationUnit::translate() precondition/assertion failed ({})\");",
            expr
        ))
        .return_expr(C::Expr::bfalse());
    c
}

fn handle_requires_assert(method: &mut C::Method, expr: &VelosiAstExpr) {
    method.body().ifelse(assert_to_cpp(expr));
}

// virtual bool do_translate(lvaddr_t src_addr, lpaddr_t *dst_addr) set_override;
fn add_translate_method_segment(c: &mut C::Class, tm: &VelosiAstMethod) {
    let src_addr_param =
        C::MethodParam::new(&tm.params[0].ident.ident, C::Type::new_typedef("lvaddr_t"));
    let _src_var = C::Expr::from_method_param(&src_addr_param);
    let dst_addr_param = C::MethodParam::new(
        "dst_addr",
        C::Type::to_ptr(&C::Type::new_typedef("lpaddr_t")),
    );
    let dst_addr = C::Expr::from_method_param(&dst_addr_param);

    let m = c
        .new_method("do_translate", C::Type::new_bool())
        .set_public()
        .set_override()
        .set_virtual()
        .push_param(src_addr_param)
        .push_param(dst_addr_param);

    m.body().raw(format!(
        "Logging::debug(\"TranslationUnit::translate(%lx)\", {})",
        &tm.params[0].ident.ident
    ));

    for e in &tm.requires {
        handle_requires_assert(m, e);
    }

    if let Some(body) = &tm.body {
        m.body()
            .assign(C::Expr::deref(&dst_addr), expr_to_cpp(body));
    }
    m.body().return_expr(C::Expr::btrue());
}

fn translate_method_enum(_e: &VelosiAstUnitEnum) -> C::Method {
    let mut m = C::Method::new("do_translate", C::Type::new_bool());
    m.body().new_return(Some(&C::Expr::bfalse()));
    m.push_param(C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t")));
    m.push_param(C::MethodParam::new(
        "dst_addr",
        C::Type::new_typedef("lpaddr_t*"),
    ));
    m
}

fn translate_method_staticmap(_s: &VelosiAstUnitStaticMap) -> C::Method {
    let mut m = C::Method::new("do_translate", C::Type::new_bool());
    m.body().new_return(Some(&C::Expr::bfalse()));
    m.push_param(C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t")));
    m.push_param(C::MethodParam::new(
        "dst_addr",
        C::Type::new_typedef("lpaddr_t*"),
    ));
    m
}

fn ast_type_to_c_type(t: &VelosiAstType) -> C::Type {
    match &t.typeinfo {
        VelosiAstTypeInfo::Integer => C::Type::new_uint(64),
        VelosiAstTypeInfo::Bool => C::Type::new_bool(),
        VelosiAstTypeInfo::GenAddr => C::Type::new_typedef("genaddr_t"),
        VelosiAstTypeInfo::VirtAddr => C::Type::new_typedef("lvaddr_t"),
        VelosiAstTypeInfo::PhysAddr => C::Type::new_typedef("lpaddr_t"),
        VelosiAstTypeInfo::Size => C::Type::new_size(),
        VelosiAstTypeInfo::Flags => C::Type::new_uint(64),
        VelosiAstTypeInfo::Range => C::Type::new_uint(64),
        VelosiAstTypeInfo::TypeRef(_) => C::Type::new_uint(64),
        VelosiAstTypeInfo::State => C::Type::new_uint(64),
        VelosiAstTypeInfo::Interface => C::Type::new_uint(64),
        VelosiAstTypeInfo::Void => C::Type::new_uint(64),
    }
}

// how is this generating both a declaration in the header file
// and an implementation in the cpp file?????
fn add_method_decl(c: &mut C::Class, tm: &VelosiAstMethod) {
    match &tm.ident.ident[..] {
        "translate" => {
            // todo figure out why this needs its own special function
            add_translate_method_segment(c, tm);
            return;
        }
        "map" => return,
        "unmap" => return,
        "protect" => return,
        _ => (),
    }

    let m = c.new_method(&tm.ident.ident, ast_type_to_c_type(&tm.rtype));
    for p in &tm.params {
        m.push_param(C::MethodParam::new(
            &p.ident.ident,
            ast_type_to_c_type(&p.ptype),
        ));
    }

    for e in &tm.requires {
        handle_requires_assert(m, e);
    }

    if let Some(body) = &tm.body {
        m.body().return_expr(expr_to_cpp(body));
    }
}

pub fn generate_unit_header(unit: &VelosiAstUnit, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    // document header
    add_header(&mut scope, unit.ident(), "unit");

    let ifn = interface_class_name(unit.ident());
    let scn = state_class_name(unit.ident());
    let ucn = unit_class_name(unit.ident());

    // set the header guard, and create
    let hdrguard = format!("{}_UNIT_HPP_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    // adding the includes
    s.new_comment("system includes");
    s.new_include("string.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", false);
    s.new_include("framework/translation_unit_base.hpp", false);

    s.new_comment("translation unit specific includes");
    s.new_include(&state_header_file(unit.ident()), false);
    s.new_include(&interface_header_file(unit.ident()), false);

    // create a new class in the scope
    let c = s.new_class(&ucn);

    c.set_base("TranslationUnitBase", C::Visibility::Public);

    add_constructor(c, &ifn, &scn);
    add_create(c, &ucn);

    // virtual UnitBase *get_interface(void) set_override
    // {
    //    return &this->_interface;
    // }
    c.new_method(
        "get_interface",
        C::Type::to_ptr(&C::Type::new_class("InterfaceBase")),
    )
    .set_public()
    // .set_virtual()
    .set_inside_def()
    .set_override()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "_interface",
    )));

    // virtual StateBase *get_state(void) set_override
    // {
    //     return &this->_state;
    // }
    c.new_method(
        "get_state",
        C::Type::to_ptr(&C::Type::new_class("StateBase")),
    )
    .set_public()
    // .set_virtual()
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

    for vrsm in unit.methods() {
        let m = c.new_method(&vrsm.ident.ident, ast_type_to_c_type(&vrsm.rtype));
        for p in &vrsm.params {
            m.push_param(C::MethodParam::new(
                &p.ident.ident,
                ast_type_to_c_type(&p.ptype),
            ));
        }
    }
    match c.method_by_name("do_translate") {
        None => {
            c.new_method("do_translate", C::Type::new_bool())
                .push_param(C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t")))
                .push_param(C::MethodParam::new(
                    "dst_addr",
                    C::Type::new_typedef("lpaddr_t*"),
                ));
        }
        Some(_) => (),
    }

    // save the scope
    let filename = unit_header_file(unit.ident());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}

pub fn generate_unit_impl(unit: &VelosiAstUnit, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    // add the header
    add_header(&mut scope, unit.ident(), "unit");

    scope.new_comment("system includes");
    scope.new_include("string.h", true);
    scope.new_include("assert.h", true);

    scope.new_comment("framework includes");
    scope.new_include("framework/types.hpp", false);
    scope.new_include("framework/logging.hpp", false);

    scope.new_comment("translation unit specific includes");
    scope.new_include(&unit_header_file(unit.ident()), false);

    // create a new class in the scope
    let ucn = unit_class_name(unit.ident());
    let c = scope.new_class(ucn.as_str());

    // c.set_base("TranslationUnitBase", C::Visibility::Public);

    let ifn = interface_class_name(unit.ident());
    let scn = state_class_name(unit.ident());

    add_constructor(c, &ifn, &scn);

    add_create(c, &ucn);

    /*
     * -------------------------------------------------------------------------------------------
     * Translations
     * -------------------------------------------------------------------------------------------
     */

    match unit {
        // segments have methods within the .vrs
        VelosiAstUnit::Segment(_) => {
            for m in unit.methods() {
                add_method_decl(c, m)
            }
        }
        // simpler units need do_translate
        VelosiAstUnit::StaticMap(s) => {
            c.push_method(translate_method_staticmap(s));
        }
        VelosiAstUnit::Enum(e) => {
            c.push_method(translate_method_enum(e));
        }
    }

    let filename = unit_impl_file(unit.ident());
    scope.set_filename(&filename);

    scope.to_file(outdir, false)?;

    Ok(())
}
