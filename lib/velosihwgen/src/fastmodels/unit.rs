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
use std::rc::Rc;
use velosiast::ast::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
    VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIfElseExpr, VelosiAstMethod,
    VelosiAstNumLiteralExpr, VelosiAstParam, VelosiAstType, VelosiAstTypeInfo, VelosiAstUnOpExpr,
    VelosiAstUnit,
};
use velosiast::{VelosiAstUnitEnum, VelosiAstUnitStaticMap};
use C::Scope;

use crate::fastmodels::add_header_comment;
use crate::fastmodels::interface::{interface_class_name, interface_header_file};
use crate::VelosiHwGenError;

pub fn unit_header_file(name: &str) -> String {
    format!("{}_unit.hpp", name)
}

pub fn unit_class_name(name: &str) -> String {
    format!("{}{}Unit", name[0..1].to_uppercase(), &name[1..])
}

pub fn state_class_name(name: &str) -> String {
    format!("{}{}State", name[0..1].to_uppercase(), &name[1..])
}

pub fn state_field_class_name(name: &str) -> String {
    format!("{}{}StateField", name[0..1].to_uppercase(), &name[1..])
}

// the C++ type name of the next unit in a page table walk
fn next_unit(unit: &VelosiAstUnit) -> Option<&Rc<String>> {
    unit.get_method("map")
        .and_then(|m| m.get_param("pa"))
        .and_then(|pa| pa.ptype.typeref())
}

fn state_field_access(access: &Vec<&str>) -> C::Expr {
    let st = C::Expr::field_access(&C::Expr::this(), "state");

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
                    // this->state.control_field()
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

// virtual bool translate(lvaddr_t src_addr, lpaddr_t *dst_addr) set_override;
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
        .new_method("translate", C::Type::new_bool())
        .set_inside_def()
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
    let mut m = C::Method::new("translate", C::Type::new_bool());
    m.body().new_return(Some(&C::Expr::bfalse()));
    m.push_param(C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t")));
    m.push_param(C::MethodParam::new(
        "dst_addr",
        C::Type::new_typedef("lpaddr_t*"),
    ));
    m
}

fn translate_method_staticmap(_s: &VelosiAstUnitStaticMap) -> C::Method {
    let mut m = C::Method::new("translate", C::Type::new_bool());
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
        VelosiAstTypeInfo::TypeRef(tr) => C::Type::new_typedef(tr),
        VelosiAstTypeInfo::State => C::Type::new_uint(64),
        VelosiAstTypeInfo::Interface => C::Type::new_uint(64),
        VelosiAstTypeInfo::Void => C::Type::new_uint(64),
    }
}

fn add_constructor(c: &mut C::Class, unit: &VelosiAstUnit, ifn: &str, scn: &str) {
    let mut arg0_type = C::Type::new_std_string();
    arg0_type.constant().reference();

    let mut arg1_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg1_type.pointer();

    let ctor = c
        .new_constructor()
        .set_inside_def(true)
        .private()
        .push_param(C::MethodParam::new("name", arg0_type.clone()))
        .push_param(C::MethodParam::new(
            "base",
            C::Type::new_typedef("lpaddr_t"),
        ))
        .push_parent_initializer(C::Expr::fn_call(
            "TranslationUnitBase",
            vec![
                C::Expr::new_var("base", C::Type::new_typedef("lpaddr_t")),
                C::Expr::new_var("name", arg0_type),
                C::Expr::new_var("ptw_pvbus", arg1_type.clone()),
            ],
        ))
        .push_initializer("state", C::Expr::fn_call(scn, vec![]))
        .push_initializer(
            "interface",
            C::Expr::fn_call(
                ifn,
                vec![C::Expr::addr_of(&C::Expr::new_var(
                    "state",
                    C::Type::new_class("Interface"),
                ))],
            ),
        );

    ctor.new_param("ptw_pvbus", arg1_type)
        .set_default_value("nullptr");

    // Filling in the state by reading data at the base addr of the unit
    match unit.state() {
        None => (),
        Some(_) => {
            let mut ctor_body = C::Block::new();
            ctor_body.method_call(C::Expr::Raw("this".to_string()), "populate_state", vec![]);
            ctor.set_body(ctor_body);
        }
    }
}

// I don't know what this function does or where its arguments should come from
fn add_create(c: &mut C::Class, ucn: &str) {
    // static TranslationUnit *create(sg::ComponentBase *parentComponent, std::string const &name,
    //     sg::CADIBase                          *cadi,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus);
    // TODO: finish

    let unit_ptr_type = C::Type::to_ptr(&C::Type::new_class(ucn));

    let m = c
        .new_method("create", unit_ptr_type.clone())
        .set_public()
        .set_static()
        .set_inside_def();

    let mut arg0_type = C::Type::new_class("sg::ComponentBase");
    arg0_type.pointer();

    let mut arg1_type = C::Type::new_std_string();
    arg1_type.constant().reference();

    let mut arg2_type = C::Type::new_class("sg::CADIBase ");
    arg2_type.pointer();

    let mut arg3_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg3_type.pointer();

    let arg4_type = C::Type::new_typedef("lpaddr_t");

    // arguments
    m.push_param(C::MethodParam::new("parentComponent", arg0_type))
        .push_param(C::MethodParam::new("name", arg1_type))
        .push_param(C::MethodParam::new("cadi", arg2_type))
        .push_param(C::MethodParam::new("ptw_pvbus", arg3_type))
        .push_param(C::MethodParam::new("base", arg4_type));

    let unitvar = C::Expr::new_var("t", unit_ptr_type.clone());

    let statevar = C::Expr::field_access(&unitvar, "state");
    let ifvar = C::Expr::field_access(&unitvar, "interface");

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
            C::Expr::Raw(format!(" new {}(name, base, ptw_pvbus)", ucn)),
        )
        // t->state.print_state_fields();
        .method_call(statevar, "print_state_fields", vec![])
        // t->interface.debug_print_interface();
        .method_call(ifvar, "debug_print_interface", vec![])
        // return t;
        .return_expr(unitvar);
}

fn add_method_maybe(c: &mut C::Class, tm: &VelosiAstMethod) {
    if c.method_by_name(&tm.ident.ident).is_some() {
        return;
    }

    let m = c
        .new_method(&tm.ident.ident, ast_type_to_c_type(&tm.rtype))
        .set_inside_def();
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

fn add_state_classes(s: &mut Scope, unit: &VelosiAstUnit) {
    let scn = state_class_name(unit.ident());
    match unit.state() {
        None => {
            s.new_class(&scn) //empty state
                .set_base("StateBase", C::Visibility::Public);
        }

        Some(state) => {
            // one class for each field
            for f in state.fields() {
                let rcn = state_field_class_name(f.ident());
                let f_c = s
                    .new_class(&rcn)
                    .set_base("StateFieldBase", C::Visibility::Public);

                let cons = f_c.new_constructor().set_inside_def(true);
                cons.push_parent_initializer(C::Expr::fn_call(
                    "StateFieldBase",
                    vec![
                        C::Expr::new_str(f.ident()),
                        C::Expr::new_num(f.size()),
                        C::Expr::new_num(0),
                    ],
                ));

                for sl in &f.layout_as_slice().to_vec() {
                    cons.body().method_call(
                        C::Expr::this(),
                        "add_slice",
                        vec![
                            C::Expr::new_str(sl.ident()),
                            C::Expr::new_num(sl.start),
                            C::Expr::new_num(sl.end),
                        ],
                    );
                }

                let var = C::Expr::new_var("data", C::Type::new_uint(64));

                // TODO: The per-slice getters and setters may or may not be helpful.
                // Keeping them for now, but I don't plan to call them
                for sl in &f.layout_as_slice().to_vec() {
                    let sl_getter_f = format!("get_{}_val", sl.ident());
                    let m = f_c
                        .new_method(&sl_getter_f, C::Type::new_uint(64))
                        .set_public()
                        .set_inline();

                    m.body().return_expr(C::Expr::method_call(
                        &C::Expr::this(),
                        "get_slice_value",
                        vec![C::Expr::new_str(sl.ident())],
                    ));
                    let sl_setter_f = format!("set_{}_val", sl.ident());
                    let m = f_c
                        .new_method(&sl_setter_f, C::Type::new_void())
                        .set_public()
                        .set_inline();
                    m.new_param("data", C::Type::new_int(64));
                    m.body().method_call(
                        C::Expr::this(),
                        "set_slice_value",
                        vec![C::Expr::new_str(sl.ident()), var.clone()],
                    );
                }
            }

            // one class for state containing all fields
            let c = s.new_class(&scn);
            c.set_base("StateBase", C::Visibility::Public);
            let state_cons = c.new_constructor().set_inside_def(true);

            for f in state.fields() {
                let fieldname = f.ident();
                let fieldclass = state_field_class_name(f.ident());
                state_cons
                    .push_initializer(fieldname.as_str(), C::Expr::fn_call(&fieldclass, vec![]));

                let this = C::Expr::this();
                let field = C::Expr::field_access(&this, fieldname);
                state_cons.body().method_call(
                    C::Expr::this(),
                    "add_field",
                    vec![C::Expr::addr_of(&field)],
                );
            }

            for f in state.fields() {
                let ty = C::BaseType::Class(state_field_class_name(f.ident()));
                c.new_attribute(f.ident(), C::Type::new(ty))
                    .set_visibility(C::Visibility::Public);
            }
        }
    }
}

fn add_interface_class(s: &mut Scope, unit: &VelosiAstUnit) {
    let ifn = interface_class_name(unit.ident());
    s.new_class(&ifn)
        .set_base("InterfaceBase", C::Visibility::Public)
        .push_doc_str("unused");
}

fn add_unit_class(s: &mut Scope, ucn: String, unit: &VelosiAstUnit, ifn: String, scn: String) {
    // create a new class in the scope
    let c = s.new_class(&ucn);
    c.set_base("TranslationUnitBase", C::Visibility::Public);

    add_constructor(c, &unit, &ifn, &scn);
    add_create(c, &ucn);

    // overrides virtual interface getter
    c.new_method(
        "get_interface",
        C::Type::to_ptr(&C::Type::new_class("InterfaceBase")),
    )
    .set_public()
    .set_inside_def()
    .set_override()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "interface",
    )));

    c.new_method(
        "get_state",
        C::Type::to_ptr(&C::Type::new_class("StateBase")),
    )
    .set_public()
    .set_inside_def()
    .set_override()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "state",
    )));

    // add the state attribute
    c.new_attribute("state", C::Type::new_class(&scn));
    c.new_attribute("interface", C::Type::new_class(&ifn));

    match unit {
        // segments have methods within the .vrs
        VelosiAstUnit::Segment(_) => {
            match unit.get_method("translate") {
                Some(tm) => add_translate_method_segment(c, &tm),
                None => panic!("segment with no explicit translate"),
            }

            for m in unit.methods() {
                add_method_maybe(c, m)
            }
        }
        // simpler units have an implicit translate function
        VelosiAstUnit::StaticMap(s) => {
            c.push_method(translate_method_staticmap(s));
        }
        VelosiAstUnit::Enum(e) => {
            c.push_method(translate_method_enum(e));
        }
    }
}

pub fn generate_unit_header(unit: &VelosiAstUnit, outdir: &Path) -> Result<(), VelosiHwGenError> {
    let mut scope = C::Scope::new();

    add_header_comment(&mut scope, unit.ident(), "top-level file");

    let ifn = interface_class_name(unit.ident());
    let scn = state_class_name(unit.ident());
    let ucn = unit_class_name(unit.ident());

    let header_guard = format!("{}_UNIT_HPP_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&header_guard);
    let s = guard.guard().then_scope();

    s.new_comment("system includes");
    s.new_include("string.h", true);
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);

    s.new_comment("framework includes");
    s.new_include("framework/types.hpp", false);
    s.new_include("framework/state_base.hpp", false);
    s.new_include("framework/state_field_base.hpp", false);
    s.new_include("framework/interface_base.hpp", false);
    s.new_include("framework/translation_unit_base.hpp", false);
    s.new_include("framework/logging.hpp", false);

    match next_unit(unit) {
        Some(u) => {
            s.new_comment("translation unit specific includes");
            s.new_include(&format!("{u}_unit.hpp"), false);
        }
        None => (),
    }

    add_state_classes(s, unit);
    add_interface_class(s, unit);
    add_unit_class(s, ucn, unit, ifn, scn);

    let filename = unit_header_file(unit.ident());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}
