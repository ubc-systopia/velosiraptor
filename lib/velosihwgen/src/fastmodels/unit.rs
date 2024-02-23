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
use std::collections::HashSet;
use std::path::Path;
use std::rc::Rc;
use velosiast::ast::{
    VelosiAstBinOp, VelosiAstBinOpExpr, VelosiAstBoolLiteralExpr, VelosiAstExpr,
    VelosiAstFnCallExpr, VelosiAstIdentLiteralExpr, VelosiAstIfElseExpr, VelosiAstMethod,
    VelosiAstNumLiteralExpr, VelosiAstStaticMap, VelosiAstType, VelosiAstTypeInfo,
    VelosiAstUnOpExpr, VelosiAstUnit, VelosiAstUnitSegment,
};
use velosiast::{
    VelosiAst, VelosiAstInterface, VelosiAstInterfaceField, VelosiAstInterfaceMemoryField,
    VelosiAstInterfaceMmioField, VelosiAstStateField, VelosiAstUnitEnum, VelosiAstUnitStaticMap,
};
use C::Scope;

use crate::fastmodels::add_header_comment;
use crate::VelosiHwGenError;

pub fn unit_header_file(name: &str) -> String {
    format!("{}_unit.hpp", name)
}

pub fn unit_impl_file(name: &str) -> String {
    format!("{}_unit.cpp", name)
}

pub fn unit_class_name(name: &str) -> String {
    format!("{}{}", name[0..1].to_uppercase(), &name[1..])
}

pub fn interface_class_name(name: &str) -> String {
    format!("{}Interface", unit_class_name(name))
}

pub fn state_class_name(name: &str) -> String {
    format!("{}State", unit_class_name(name))
}

pub fn state_field_class_name(unit: &str, name: &str) -> String {
    format!(
        "{}{}{}StateField",
        unit_class_name(unit),
        name[0..1].to_uppercase(),
        &name[1..]
    )
}

// the C++ type name of the next unit in a page table walk
fn next_unit(unit: &VelosiAstUnit) -> Option<&Rc<String>> {
    unit.get_method("map")
        .and_then(|m| m.get_param("pa"))
        .and_then(|pa| pa.ptype.typeref())
}

fn state_field_access(access: &[&str], unit: Option<&C::Expr>) -> C::Expr {
    let st = if let Some(unit) = unit {
        C::Expr::field_access(unit, "state")
    } else {
        C::Expr::field_access(&C::Expr::this(), "state")
    };

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

/// flattens an if-else expression by combining the branches with the conditional:
///
/// if A { 1 } else { 2 }  -> (A, 1), (!A, 2)
/// if A { if B {1} else {2} } else { if C {3} else {4} } -> (A&&B, 1), (A&&!B, 2), (!A&&C, 3), (!A&&!C, 4)
///
/// a + if A { 1 } else { 2 } -> (A, a+1), (!A, a+2)
fn flatten_if_else_expr(expr: &Rc<VelosiAstExpr>) -> Vec<(Rc<VelosiAstExpr>, Rc<VelosiAstExpr>)> {
    match expr.as_ref() {
        VelosiAstExpr::IfElse(VelosiAstIfElseExpr {
            cond, then, other, ..
        }) => {
            let mut res: Vec<_> = flatten_if_else_expr(then)
                .into_iter()
                .map(|(c, expr)| {
                    let cond_new = if let VelosiAstExpr::BoolLiteral(_) = c.as_ref() {
                        cond.clone()
                    } else {
                        VelosiAstExpr::BinOp(VelosiAstBinOpExpr::land(cond.clone(), c)).into()
                    };

                    (cond_new, expr)
                })
                .collect();

            res.extend(
                flatten_if_else_expr(other)
                    .into_iter()
                    .map(|(c, expr)| {
                        let cond_new = if let VelosiAstExpr::BoolLiteral(_) = c.as_ref() {
                            VelosiAstUnOpExpr::new_lnot(cond.clone()).into()
                        } else {
                            VelosiAstExpr::BinOp(VelosiAstBinOpExpr::land(
                                VelosiAstUnOpExpr::new_lnot(cond.clone()).into(),
                                c,
                            ))
                            .into()
                        };

                        (cond_new, expr)
                    })
                    .collect::<Vec<_>>(),
            );

            res
        }
        VelosiAstExpr::BinOp(VelosiAstBinOpExpr { lhs, op, rhs, loc }) => {
            let lhs = flatten_if_else_expr(lhs);
            let rhs = flatten_if_else_expr(rhs);

            // they should not be empty
            debug_assert!(!lhs.is_empty());
            debug_assert!(!rhs.is_empty());

            if lhs.len() == 1 && rhs.len() == 1 {
                // both branches have a single operand, simply ignore and return the original
                vec![(
                    VelosiAstExpr::BoolLiteral(VelosiAstBoolLiteralExpr::btrue()).into(),
                    expr.clone(),
                )]
            } else {
                // build the cross product of all the two operands,
                // a + if C { 1 } else { 2 } => [(true, a)]  [ (C, 1), (!C, 2) ] => [(C, a+1), (!C, a+2)]
                // if A { 1 } else { 2 } + if B { 3 } else { 4 } => [(A, 1), (!A, 2)] [(B, 3), (!B, 4)]
                // => [(A&&B, 1+3), (A && !B, 1+3), (!A&&B, 2+3), (!A&&!B, 2+3))]
                let mut res = Vec::with_capacity(lhs.len() * rhs.len());
                for (c1, e1) in &lhs {
                    for (c2, e2) in &rhs {
                        let e = VelosiAstExpr::BinOp(VelosiAstBinOpExpr::new(
                            e1.clone(),
                            *op,
                            e2.clone(),
                            loc.clone(),
                        ));
                        if let VelosiAstExpr::BoolLiteral(_) = c1.as_ref() {
                            res.push((c2.clone(), e.into()))
                        } else if let VelosiAstExpr::BoolLiteral(_) = c2.as_ref() {
                            res.push((c1.clone(), e.into()))
                        } else {
                            let c = VelosiAstExpr::BinOp(VelosiAstBinOpExpr::land(
                                c1.clone(),
                                c2.clone(),
                            ));
                            res.push((c.into(), e.into()));
                        }
                    }
                }
                res
            }
        }
        VelosiAstExpr::UnOp(VelosiAstUnOpExpr { op: _, expr: _, .. }) => {
            unimplemented!()
        }
        VelosiAstExpr::Quantifier(_) => {
            unimplemented!()
        }
        VelosiAstExpr::FnCall(_) => {
            unimplemented!()
        }
        VelosiAstExpr::Slice(_) => {
            unimplemented!()
        }
        VelosiAstExpr::Range(_) => {
            unimplemented!()
        }
        _ => vec![(
            VelosiAstExpr::BoolLiteral(VelosiAstBoolLiteralExpr::btrue()).into(),
            expr.clone(),
        )],
    }
}

fn expr_to_cpp_with_unit(
    expr: &VelosiAstExpr,
    params: &HashSet<&str>,
    unit: Option<&C::Expr>,
) -> C::Expr {
    use VelosiAstExpr::*;
    match expr {
        IdentLiteral(VelosiAstIdentLiteralExpr { ident, .. }) => {
            let p: Vec<&str> = ident.path_split().collect();
            match p[0] {
                "state" => {
                    // this->state.control_field()
                    state_field_access(&p, unit)
                }
                "interface" => panic!("interface not implemented"),
                "flgs" => {
                    // C::Expr::new_var(ident.as_str() , C::Type::new_int(64))
                    C::Expr::new_var("flgs", C::Type::new_int(64))
                }
                x => {
                    if params.contains(x) {
                        C::Expr::field_access(&C::Expr::this(), x)
                    } else {
                        C::Expr::new_var(x, C::Type::new_int(64))
                    }
                }
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
            let e = expr_to_cpp_with_unit(lhs, params, unit);
            let e2 = expr_to_cpp_with_unit(rhs, params, unit);
            // implies "==>" needs a special case, others should be fine in cpp
            match op {
                VelosiAstBinOp::Implies => C::Expr::binop(C::Expr::lnot(e), "||", e2),
                _ => C::Expr::binop(e, &format!("{}", op), e2),
            }
        }
        UnOp(VelosiAstUnOpExpr { op, expr, .. }) => {
            let o = format!("{}", op);
            let e = expr_to_cpp_with_unit(expr, params, unit);
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
                args.iter()
                    .map(|a| expr_to_cpp_with_unit(a.as_ref(), params, unit))
                    .collect(),
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
        }) => C::Expr::ternary(
            expr_to_cpp_with_unit(cond, params, unit),
            expr_to_cpp_with_unit(then, params, unit),
            expr_to_cpp_with_unit(other, params, unit),
        ),
    }
}

fn expr_to_cpp(expr: &VelosiAstExpr, params: &HashSet<&str>) -> C::Expr {
    expr_to_cpp_with_unit(expr, params, None)
}

fn assert_to_cpp(expr: &VelosiAstExpr, params: &HashSet<&str>) -> C::IfElse {
    let mut c = C::IfElse::with_expr(C::Expr::lnot(expr_to_cpp(expr, params)));
    c.then_branch()
        .raw(format!(
            "Logging::debug(\"TranslationUnit::translate() precondition/assertion failed ({})\");",
            expr
        ))
        .return_expr(C::Expr::bfalse());
    c
}

fn handle_requires_assert(method: &mut C::Method, expr: &VelosiAstExpr, params: &HashSet<&str>) {
    method.body().ifelse(assert_to_cpp(expr, params));
}

fn add_check_permissions_method_segment(c: &mut C::Class, _segment: &VelosiAstUnitSegment) {
    let src_addr_param = C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t"));
    let _src_var = C::Expr::from_method_param(&src_addr_param);

    let mode_param = C::MethodParam::new("mode", C::Type::new_typedef("access_mode_t"));
    let _mode = C::Expr::from_method_param(&mode_param);

    let m = c
        .new_method("check_permissions", C::Type::new_bool())
        .set_public()
        .set_override()
        .set_virtual()
        .push_param(src_addr_param)
        .push_param(mode_param);

    let body = m.body();

    // for m in segment.methods() {
    //     if m.properties.contains(&VelosiAstProperty::Remap) {
    //         // body.new_comment(&format!("TODO: handle {} pre condition\n", m.ident()));

    //         body.new_ifelse(&C::Expr::lnot(C::Expr::method_call(
    //             &C::Expr::this(),
    //             m.ident(),
    //             vec![],
    //         )))
    //         .then_branch()
    //         .return_expr(C::Expr::bfalse());
    //     }
    // }

    body.return_expr(C::Expr::btrue());
}

fn check_permission_nop() -> C::Method {
    let src_addr_param = C::MethodParam::new("va", C::Type::new_typedef("lvaddr_t"));
    let mode_param = C::MethodParam::new("dst_addr", C::Type::new_typedef("access_mode_t"));

    let mut m = C::Method::new("check_permissions", C::Type::new_bool());

    m.set_public()
        .set_override()
        .set_virtual()
        .push_param(src_addr_param)
        .push_param(mode_param);

    m.body().return_expr(C::Expr::btrue());

    m
}

fn construct_next_unit(
    block: &mut C::Block,
    next: &VelosiAstUnit,
    mut args: Vec<C::Expr>,
) -> C::Expr {
    block.new_comment("construct the next unit");
    let next_class_name = unit_class_name(next.ident().as_str());
    let next_class_create_fn = format!("{}::create", next_class_name);
    let next_unit = block
        .new_variable(
            "next",
            C::Type::new_class(next_class_name.as_str()).to_ptr(),
        )
        .to_expr();

    args.push(C::Expr::new_str(next_class_name.as_str()));
    args.push(C::Expr::field_access(&C::Expr::this(), "ptw_pvbus"));

    block.assign(
        next_unit.clone(),
        C::Expr::fn_call(next_class_create_fn.as_str(), args),
    );
    next_unit
}

// virtual bool MMU::translate(lvaddr_t src_addr, lpaddr_t *dst_addr) set_override;
fn add_translate_method_segment(
    c: &mut C::Class,
    segment: &VelosiAstUnitSegment,
    tm: &VelosiAstMethod,
    next: Option<&VelosiAstUnit>,
) {
    let src_addr_param =
        C::MethodParam::new(&tm.params[0].ident.ident, C::Type::new_typedef("lvaddr_t"));
    let src_var = C::Expr::from_method_param(&src_addr_param);
    let dst_addr_param = C::MethodParam::new(
        "dst_addr",
        C::Type::to_ptr(&C::Type::new_typedef("lpaddr_t")),
    );
    let dst_addr = C::Expr::from_method_param(&dst_addr_param);

    let params = segment
        .params_as_slice()
        .iter()
        .map(|p| p.ident().as_str())
        .collect();

    let m = c
        .new_method("translate", C::Type::new_bool())
        .set_public()
        .set_override()
        .set_virtual()
        .push_param(src_addr_param)
        .push_param(dst_addr_param);

    m.body().raw(format!(
        "Logging::debug(\"{}::translate(0x%lx)\", {})",
        segment.ident(),
        &tm.params[0].ident.ident
    ));

    for e in &tm.requires {
        handle_requires_assert(m, e, &params);
    }

    let body = m.body();

    let base_var = body
        .new_variable("base_new", C::Type::new_uintptr())
        .to_expr();

    if let Some(tbody) = &tm.body {
        if let Some(next) = next {
            // construct the next unit if applicable

            let flattened_body = flatten_if_else_expr(tbody);
            for (cond, expr) in flattened_body {
                let ifelse = body.new_ifelse(&expr_to_cpp(&cond, &params));
                let branch = ifelse.then_branch();

                // we have state references to this indicates we need to go to the next one
                // shouldn't we be looking at the parameters of map() instead?
                if expr.has_state_references() {
                    // calculate physical base of next unit
                    branch.assign(base_var.clone(), expr_to_cpp(&expr, &params));
                    let next_unit = construct_next_unit(branch, next, vec![base_var.clone()]);

                    match next.input_bitwidth() {
                        64 => {
                            branch.new_comment(
                                "calculate the virtual address: input bitwidth is max",
                            );
                        }
                        a => {
                            if a == segment.inbitwidth {
                                branch.new_comment("calculate the virtual address: input bitwidth match! no need to calculate the new VA");
                            } else {
                                let mask = (1 << a) - 1;
                                branch.assign(
                                    src_var.clone(),
                                    C::Expr::binop(src_var.clone(), "&", C::Expr::new_num(mask)),
                                );
                            }
                        }
                    }

                    branch
                        .new_comment("call translate on it.")
                        .return_expr(C::Expr::method_call(
                            &next_unit,
                            "translate",
                            vec![src_var.clone(), dst_addr.clone()],
                        ));
                } else {
                    // there are no state references, so the expression evaluates to the same
                    // constant value every time, return this!
                    // XXX: this is not 100% accurate, as we could construct the next unit
                    //      with this value. For now, we just use that!

                    // if cond { return expr }
                    branch
                        .assign(base_var.clone(), expr_to_cpp(&expr, &params))
                        .assign(C::Expr::deref(&dst_addr), base_var.clone())
                        .return_expr(C::Expr::btrue());
                }
            }

            body.return_expr(C::Expr::bfalse());
        } else {
            let offset_mask = body
                .new_variable("offset_mask", C::Type::new_uint64())
                .to_expr();
            body.assign(
                offset_mask.clone(),
                C::Expr::Raw(format!("((uint64_t)1 << {:#x}) - 1", segment.inbitwidth)),
            );

            // should always be dealing with paddrs
            // return the expression
            // no next translation unit, simply set the return value with the expression
            body.new_comment("return the result of the translation");
            // calculate the value
            body.assign(
                base_var.clone(),
                C::Expr::binop(
                    expr_to_cpp(tbody, &params),
                    "+",
                    C::Expr::binop(src_var, "&", offset_mask),
                ),
            );
            // assign it to the deref return value
            body.assign(C::Expr::deref(&dst_addr), base_var);
            // return true
            body.return_expr(C::Expr::btrue());
        }
    } else {
        body.assign(base_var.clone(), C::Expr::Raw(String::from("PANIC!")));
    }
}

fn translate_method_enum(unit: &VelosiAstUnitEnum, ast: &VelosiAst) -> C::Method {
    let mut m = C::Method::new("translate", C::Type::new_bool());
    m.set_public();

    // function parameters
    let va_param = m.new_param("va", C::Type::new_typedef("lvaddr_t"));
    let va_var = va_param.to_expr();

    let dst_param = m.new_param("dst_addr", C::Type::new_typedef("lpaddr_t").to_ptr());
    let dst_var = dst_param.to_expr();

    // construct the function body
    let params = unit
        .params_as_slice()
        .iter()
        .map(|p| p.ident().as_str())
        .collect();

    let body = m.body();
    for variant in unit.enums.values() {
        let block = body.new_dowhile_loop(&C::Expr::bfalse()).body();

        let next_unit = ast
            .get_unit(variant.ident.as_str())
            .expect("undefined unit?");

        let args = variant
            .args
            .iter()
            .map(|a| C::Expr::field_access(&C::Expr::this(), a.ident().as_str()))
            .collect();
        let next = construct_next_unit(block, next_unit, args);

        let cond = variant.differentiator.iter().skip(1).fold(
            expr_to_cpp_with_unit(&variant.differentiator[0], &params, Some(&next)),
            |cond, e| C::Expr::binop(cond, "&&", expr_to_cpp_with_unit(e, &params, Some(&next))),
        );

        block
            .new_ifelse(&cond)
            .then_branch()
            .return_expr(C::Expr::method_call(
                &next,
                "translate",
                vec![va_var.clone(), dst_var.clone()],
            ));
    }

    body.new_return(Some(&C::Expr::bfalse()));

    m
}

fn translate_method_staticmap(s: &VelosiAstUnitStaticMap, ast: &VelosiAst) -> C::Method {
    // function name and properties
    let mut m = C::Method::new("translate", C::Type::new_bool());
    m.set_public();

    // function parameters
    let va_param = m.new_param("va", C::Type::new_typedef("lvaddr_t"));
    let va_var = va_param.to_expr();

    let dst_param = m.new_param("dst_addr", C::Type::new_typedef("lpaddr_t").to_ptr());
    let dst_var = dst_param.to_expr();

    // construct the function body
    let params = s
        .params_as_slice()
        .iter()
        .map(|p| p.ident().as_str())
        .collect();

    let body = m.body();

    match &s.map {
        VelosiAstStaticMap::Explicit(map) => {
            let mut start_address = 0;
            for entry in &map.entries {
                if let Some(_src) = &entry.src {
                    panic!("TODO: handle me!");
                }

                let unit_size = 1 << entry.dst_bitwidth;

                let next_unit = ast.get_unit(entry.dst.ident()).expect("undefined unit?");

                let mut args = Vec::new();
                for arg in &entry.dst.args {
                    args.push(expr_to_cpp(arg, &params));
                }

                // if start_address <= va_var < start_address + entry.size
                let cond = C::Expr::binop(
                    C::Expr::binop(C::Expr::new_num(start_address), "<=", va_var.clone()),
                    "&&",
                    C::Expr::binop(
                        va_var.clone(),
                        "<",
                        C::Expr::new_num(start_address + unit_size),
                    ),
                );

                //
                let then = body.new_ifelse(&cond).then_branch();

                for p in &s.params {
                    let v = then
                        .new_variable(p.ident().as_str(), ast_type_to_c_type(&p.ptype))
                        .to_expr();
                    then.assign(
                        v,
                        C::Expr::field_access(
                            &C::Expr::this(),
                            &format!("_{}", p.ident().as_str()),
                        ),
                    );
                }

                let next_unit = construct_next_unit(then, next_unit, args);

                body.method_call(
                    next_unit,
                    "translate",
                    vec![
                        C::Expr::binop(va_var.clone(), "-", C::Expr::new_num(start_address)),
                        dst_var.clone(),
                    ],
                );

                start_address += unit_size;
            }

            body.fn_call(
                "Logging::warn",
                vec![C::Expr::new_str("Cannot handle this type of map")],
            )
            .return_expr(C::Expr::bfalse());
        }
        VelosiAstStaticMap::ListComp(map) => {
            if let Some(_src) = &map.elm.src {
                panic!("TODO: handle me!");
            }

            // let element_size = 1 << map.elm.dst_bitwidth;
            let indexbits = map.range.end.trailing_zeros(); // 9 in x86
            if map.range.end - (1 << indexbits) != 0 {
                panic!("TODO: handle odd page size")
            }

            // mask = ((1 << indexbits) - 1) << bitwidth
            let idx_mask = body
                .new_variable("idx_mask", C::Type::new_uint64())
                .to_expr();
            body.assign(
                idx_mask.clone(),
                C::Expr::Raw(format!(
                    "(((uint64_t)1 << {:#x}) - 1) << {:#x}",
                    indexbits, map.elm.dst_bitwidth
                )),
            );

            let idx_var = body
                .new_variable(map.var.ident(), C::Type::new_uint64())
                .to_expr();
            body.assign(
                idx_var.clone(),
                C::Expr::binop(
                    C::Expr::binop(idx_mask, "&", va_var.clone()),
                    ">>",
                    C::Expr::new_num(map.elm.dst_bitwidth),
                ),
            );

            body.fn_call(
                "Logging::debug",
                vec![
                    C::Expr::new_str("translating with map[0x%lx]"),
                    idx_var.clone(),
                ],
            );

            let mut args = Vec::new();
            // args.push(C::Expr::Raw(format!("this->base + {}", idx_var.clone())));

            for arg in &map.elm.dst.args {
                args.push(expr_to_cpp(arg, &params));
            }

            let next_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
            let next_var = construct_next_unit(body, next_unit, args);

            // va = va - (idx * element_size);
            body.new_comment("construct the new variable value");
            // body.assign(
            //     va_var.clone(),
            //     C::Expr::binop(
            //         va_var.clone(),
            //         "-",
            //         C::Expr::binop(idx_var.clone(), "*", C::Expr::new_num(element_size)),
            //     ),
            // );

            body.return_expr(C::Expr::method_call(
                &next_var,
                "translate",
                vec![va_var, dst_var],
            ));
        }
        _ => {
            body.fn_call(
                "Logging::warn",
                vec![C::Expr::new_str("Cannot handle this type of map")],
            )
            .return_expr(C::Expr::bfalse());
        }
    }

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
        VelosiAstTypeInfo::Extern(_) => unreachable!(),
        VelosiAstTypeInfo::State => C::Type::new_uint(64),
        VelosiAstTypeInfo::Interface => C::Type::new_uint(64),
        VelosiAstTypeInfo::Void => C::Type::new_uint(64),
        VelosiAstTypeInfo::SelfType => C::Type::new_uint(64),
    }
}

fn add_constructor(c: &mut C::Class, unit: &VelosiAstUnit, ifn: &str, scn: &str) {
    let mut arg0_type = C::Type::new_std_string();
    arg0_type.constant().reference();

    let mut arg1_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg1_type.pointer();

    let ctor = c.new_constructor().private();

    ctor.push_parent_initializer(C::Expr::fn_call(
        "TranslationUnitBase",
        vec![
            C::Expr::new_var("base", C::Type::new_typedef("lpaddr_t")),
            C::Expr::new_var("name", arg0_type.clone()),
            C::Expr::new_var("ptw_pvbus", arg1_type.clone()),
        ],
    ))
    .push_initializer(
        "state",
        C::Expr::fn_call(
            scn,
            vec![
                C::Expr::new_var("base", C::Type::new_typedef("lpaddr_t")),
                C::Expr::new_var("ptw_pvbus", arg1_type.clone()),
            ],
        ),
    )
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

    // parameters
    for param in unit.params_as_slice() {
        let p = ctor
            .new_param(param.ident().as_str(), ast_type_to_c_type(&param.ptype))
            .to_expr();
        ctor.push_initializer(param.ident().as_str(), p);
    }
    ctor.push_param(C::MethodParam::new("name", arg0_type.clone()));
    ctor.new_param("ptw_pvbus", arg1_type.clone())
        .set_default_value("nullptr");

    // Filling in the state by reading data at the base addr of the unit
    match unit.state() {
        None => (),
        Some(_) => {
            let mut ctor_body = C::Block::new();
            ctor_body.fn_call("this->state.populate_state", vec![]);
            ctor.set_body(ctor_body);
        }
    }
}

fn add_create(c: &mut C::Class, unit: &VelosiAstUnit) {
    // static TranslationUnit *create(sg::ComponentBase *parentComponent, std::string const &name,
    //     sg::CADIBase                          *cadi,
    //     pv::RandomContextTransactionGenerator *ptw_pvbus);
    // TODO: finish

    let ucn = unit_class_name(unit.ident());

    let unit_ptr_type = C::Type::to_ptr(&C::Type::new_class(&ucn));

    let m = c
        .new_method("create", unit_ptr_type.clone())
        .set_public()
        .set_static();

    // let mut arg0_type = C::Type::new_class("sg::ComponentBase");
    // arg0_type.pointer();

    let mut args = Vec::new();
    unit.params_as_slice().iter().for_each(|p| {
        args.push(
            m.new_param(p.ident().as_str(), ast_type_to_c_type(&p.ptype))
                .to_expr(),
        );
    });

    // argument for a name
    let mut arg1_type = C::Type::new_std_string();
    arg1_type.constant().reference();
    args.push(m.new_param("name", arg1_type).to_expr());

    // pointer to the page table walker
    let mut arg3_type = C::Type::new_class("pv::RandomContextTransactionGenerator");
    arg3_type.pointer();
    args.push(m.new_param("ptw_pvbus", arg3_type).to_expr());

    let unitvar = C::Expr::new_var("t", unit_ptr_type.clone());
    let statevar = C::Expr::field_access(&unitvar, "state");
    let _ifvar = C::Expr::field_access(&unitvar, "interface");

    //  TranslationUnit *t;
    m.body()
        .variable(C::Variable::new("t", unit_ptr_type))
        .fn_call(
            "Logging::debug",
            vec![C::Expr::new_str("Create translation unit")],
        )
        // t = new TranslationUnit(name, ptw_pvbus)
        .assign(unitvar.clone(), C::Expr::new(&ucn, args))
        // t->state.print_state_fields();
        .method_call(statevar, "print_state_fields", vec![])
        // t->interface.debug_print_interface();
        // .method_call(ifvar, "debug_print_interface", vec![])
        // return t;
        .return_expr(unitvar);
}

fn add_method_maybe(c: &mut C::Class, tm: &VelosiAstMethod, params: &HashSet<&str>) {
    if c.method_by_name(&tm.ident.ident).is_some() {
        return;
    }

    // various todo functions
    match &tm.ident.ident[..] {
        "map" => return,
        "unmap" => return,
        "protect" => return,
        "translate" => return,
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
        handle_requires_assert(m, e, params);
    }

    if let Some(body) = &tm.body {
        m.body().return_expr(expr_to_cpp(body, params));
    }
}

fn add_state_classes(s: &mut Scope, unit: &VelosiAstUnit) {
    let scn = state_class_name(unit.ident());

    let state_fields: Vec<Rc<VelosiAstStateField>> = match unit.state() {
        Some(s) => s.fields().to_vec(),
        None => Vec::<Rc<VelosiAstStateField>>::new(),
    };

    for f in state_fields.clone() {
        let sfcn = state_field_class_name(unit.ident(), f.ident());
        let f_c = s
            .new_class(&sfcn)
            .set_base("StateFieldBase", C::Visibility::Public);

        let sf_offset = unit
            .interface()
            .and_then(|i: Rc<VelosiAstInterface>| i.fields_map.get(&f.ident_to_string()).cloned())
            .and_then(|i_f| match i_f.as_ref() {
                VelosiAstInterfaceField::Mmio(VelosiAstInterfaceMmioField { offset, .. })
                | VelosiAstInterfaceField::Memory(VelosiAstInterfaceMemoryField {
                    offset, ..
                }) => Some(offset.clone() * 8),
                _ => Some(0),
            });

        let offset = match sf_offset {
            Some(o) => o,
            None => {
                println!(
                    "Warning: no memory or MMIO interface found for field {}",
                    f.ident()
                );
                0
            }
        };

        let cons = f_c.new_constructor();
        cons.push_param(C::MethodParam::new(
            "base",
            C::Type::new_typedef("lpaddr_t"),
        ));
        cons.push_param(C::MethodParam::new(
            "ptw_pvbus",
            C::Type::new_class("pv::RandomContextTransactionGenerator *"),
        ));

        cons.push_parent_initializer(C::Expr::fn_call(
            "StateFieldBase",
            vec![
                C::Expr::new_str(f.ident()),
                C::Expr::new_num(offset),
                C::Expr::Raw(String::from("base")),
                C::Expr::Raw(String::from("ptw_pvbus")),
                C::Expr::new_num(f.size() * 8),
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
                    // C++ side uses inclusive-inclusive bounds (todo: change)
                    C::Expr::new_num(sl.end - 1),
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
                .set_public();

            m.body().return_expr(C::Expr::method_call(
                &C::Expr::this(),
                "get_slice_value",
                vec![C::Expr::new_str(sl.ident())],
            ));
            let sl_setter_f = format!("set_{}_val", sl.ident());
            let m = f_c
                .new_method(&sl_setter_f, C::Type::new_void())
                .set_public();
            m.new_param("data", C::Type::new_int(64));
            m.body().method_call(
                C::Expr::this(),
                "set_slice_value",
                vec![C::Expr::new_str(sl.ident()), var.clone()],
            );
        }
    }

    // one class for state containing all fields
    let state_class = s.new_class(&scn);
    state_class.set_base("StateBase", C::Visibility::Public);
    let state_cons = state_class.new_constructor();

    state_cons.push_param(C::MethodParam::new(
        "base",
        C::Type::new_typedef("lpaddr_t"),
    ));
    state_cons.push_param(C::MethodParam::new(
        "ptw_pvbus",
        C::Type::new_class("pv::RandomContextTransactionGenerator *"),
    ));

    state_cons.push_parent_initializer(C::Expr::fn_call(
        "StateBase",
        vec![
            C::Expr::Raw(String::from("base")),
            C::Expr::Raw(String::from("ptw_pvbus")),
        ],
    ));

    for f in state_fields.clone() {
        let fieldname = f.ident();
        let fieldclass = state_field_class_name(unit.ident(), f.ident());
        state_cons.push_initializer(
            fieldname.as_str(),
            C::Expr::fn_call(
                &fieldclass,
                vec![
                    C::Expr::Raw(String::from("base")),
                    C::Expr::Raw(String::from("ptw_pvbus")),
                ],
            ),
        );

        let this = C::Expr::this();
        let field = C::Expr::field_access(&this, fieldname);
        state_cons
            .body()
            .method_call(C::Expr::this(), "add_field", vec![C::Expr::addr_of(&field)]);
    }

    for f in state_fields {
        let ty = C::BaseType::Class(state_field_class_name(unit.ident(), f.ident()));
        state_class
            .new_attribute(f.ident(), C::Type::new(ty))
            .set_visibility(C::Visibility::Public);
    }
}

fn add_interface_class(s: &mut Scope, unit: &VelosiAstUnit) {
    let ifn = interface_class_name(unit.ident());
    let c = s
        .new_class(&ifn)
        .set_base("InterfaceBase", C::Visibility::Public)
        .push_doc_str("unused");

    let scn = state_class_name(unit.ident());
    let state_ptr_type = C::Type::to_ptr(&C::Type::new_class(&scn));

    c.new_attribute("_state", state_ptr_type.clone());

    let cons = c.new_constructor();

    let m = cons.new_param("state", state_ptr_type);

    let pa = C::Expr::from_method_param(m);

    cons.push_parent_initializer(C::Expr::fn_call("InterfaceBase", vec![pa.clone()]));
    cons.push_initializer("_state", pa);
}

fn add_unit_class(s: &mut Scope, unit: &VelosiAstUnit, ast: &VelosiAst) {
    let ifn = interface_class_name(unit.ident());
    let scn = state_class_name(unit.ident());
    let ucn = unit_class_name(unit.ident());

    // create a new class in the scope
    let c = s.new_class(&ucn);
    c.set_base("TranslationUnitBase", C::Visibility::Public);

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Adding the constructors and attributes
    ////////////////////////////////////////////////////////////////////////////////////////////////

    add_constructor(c, unit, &ifn, &scn);
    add_create(c, unit);

    c.new_attribute("state", C::Type::new_class(&scn))
        .set_public();
    c.new_attribute("interface", C::Type::new_class(&ifn))
        .set_public();

    for p in unit.params_as_slice() {
        c.new_attribute(p.ident(), ast_type_to_c_type(&p.ptype));
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Overriding methods to obtain the interface / state references
    ////////////////////////////////////////////////////////////////////////////////////////////////

    // overrides virtual interface getter
    c.new_method(
        "get_interface",
        C::Type::to_ptr(&C::Type::new_class("InterfaceBase")),
    )
    .set_public()
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
    .set_override()
    .body()
    .return_expr(C::Expr::addr_of(&C::Expr::field_access(
        &C::Expr::this(),
        "state",
    )));

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Adding the methods and translate behavior
    ////////////////////////////////////////////////////////////////////////////////////////////////

    let params = unit
        .params_as_slice()
        .iter()
        .map(|p| p.ident().as_str())
        .collect();
    for m in unit.methods() {
        add_method_maybe(c, m, &params);
    }

    match unit {
        // segments have methods within the .vrs
        VelosiAstUnit::Segment(s) => {
            let tm = s
                .get_method("translate")
                .expect("translate method not found");
            let next = if let Some(next) = next_unit(unit) {
                ast.get_unit(next)
            } else {
                None
            };

            add_translate_method_segment(c, s, tm, next);
            add_check_permissions_method_segment(c, s);
        }
        // simpler units have an implicit translate function
        VelosiAstUnit::StaticMap(s) => {
            c.push_method(translate_method_staticmap(s, ast));
            c.push_method(check_permission_nop());
        }
        VelosiAstUnit::Enum(e) => {
            c.push_method(translate_method_enum(e, ast));
            c.push_method(check_permission_nop());
        }
        VelosiAstUnit::OSSpec(_) => (),
    }
}

// Main function here: generates cpp + hpp for unit.
// Some duplication since calling clone() on crustal's Scope wasn't working as expected.
pub fn generate_unit_cpp(
    unit: &VelosiAstUnit,
    ast: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiHwGenError> {
    let mut hs = C::Scope::new();

    let header_guard = format!("{}_UNIT_HPP_", unit.ident().to_uppercase());
    let guard = hs.new_ifdef(&header_guard);
    hs = guard.guard().then_scope().clone();

    add_header_comment(&mut hs, unit.ident(), "generated implementation");

    hs.new_comment("system includes");
    hs.new_include("string.h", true);
    hs.new_include("stddef.h", true);
    hs.new_include("assert.h", true);
    hs.new_comment("framework includes");
    hs.new_include("framework/types.hpp", false);
    hs.new_include("framework/state_base.hpp", false);
    hs.new_include("framework/state_field_base.hpp", false);
    hs.new_include("framework/interface_base.hpp", false);
    hs.new_include("framework/translation_unit_base.hpp", false);
    hs.new_include("framework/logging.hpp", false);
    hs.new_include("framework/fm_util.hpp", false);

    for u in unit.get_next_unit_idents() {
        hs.new_comment("translation unit specific includes");
        hs.new_include(&unit_header_file(&u.to_string()), false);
    }

    add_state_classes(&mut hs, unit);
    add_interface_class(&mut hs, unit);
    add_unit_class(&mut hs, unit, ast);

    hs.set_filename(&unit_header_file(unit.ident()));
    hs.to_file(outdir, true)?;

    let mut is = C::Scope::new();
    is.new_include(&unit_header_file(unit.ident()), false);

    add_state_classes(&mut is, unit);
    add_interface_class(&mut is, unit);
    add_unit_class(&mut is, unit, ast);

    add_header_comment(&mut is, unit.ident(), "generated implementation");

    is.set_filename(&unit_impl_file(unit.ident()));
    is.to_file(outdir, false)?;

    Ok(())
}
