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

//! Segment Code Generation (C)

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::rc::Rc;

use crustal as C;

use velosiast::ast::{VelosiAstMethod, VelosiAstTypeInfo, VelosiAstUnitSegment};
use velosiast::{VelosiAst, VelosiAstTypeProperty, VelosiAstUnit};
use velosicomposition::Relations;

use super::utils::{self, FieldUtils, UnitUtils};
use crate::VelosiCodeGenError;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helpers
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_fn_params<'a>(
    fun: &mut C::Function,
    unit: &VelosiAstUnitSegment,
    op: &'a VelosiAstMethod,
    osspec: &VelosiAst,
    higher_order: bool,
) -> (
    HashMap<&'a str, C::Expr>,
    HashMap<&'a str, VelosiAstTypeInfo>,
) {
    let env = osspec.osspec().unwrap();

    let mut param_exprs = HashMap::new();
    let mut param_types = HashMap::new();

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("$unit", unit_param.clone());
    param_types.insert(
        "$unit",
        VelosiAstTypeInfo::TypeRef(Rc::new(unit.to_type_name())),
    );

    for f in op.params.iter() {
        let p = if f.ident().as_str() == "pa" && higher_order {
            if let Some(ty) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                param_types.insert(
                    f.ident().as_str(),
                    VelosiAstTypeInfo::Extern(ty.ident.ident.clone()),
                );
                fun.new_param(f.ident(), C::Type::new_typedef(ty.ident.as_str()))
            } else {
                param_types.insert(f.ident().as_str(), f.ptype.typeinfo.clone());
                fun.new_param(
                    f.ident(),
                    unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, true),
                )
            }
        } else {
            param_types.insert(f.ident().as_str(), f.ptype.typeinfo.clone());
            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true))
        };
        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    (param_exprs, param_types)
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////////////////////////

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &VelosiAstUnitSegment) {
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    scope.new_comment("Defined unit constants");
    for c in unit.consts() {
        utils::add_const_def(scope, c);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constructors
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_unit_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    if !env.has_map_protect_unmap() {
        // handled elsewhere!
        return;
    }

    let mut s = C::Struct::new(&unit.to_struct_name());
    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

    let stype = s.to_type();

    // Add a field for the VNode type as this is a translation table
    if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor) {
        let f = C::Field::with_string(
            String::from("vnode"),
            unit.ptype_to_ctype(&etype.as_ref().into(), false),
        );
        s.push_field(f);
    } else {
        unimplemented!("expected a frame type!");
    }

    if unit.maps_frame() {
        if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
            let f = C::Field::with_string(
                String::from("frame"),
                unit.ptype_to_ctype(&etype.as_ref().into(), false),
            );
            s.push_field(f);
        } else {
            unimplemented!("expected a frame type!");
        }
    } else if unit.maps_table() {
        // here we just have a pointer to the next field
        let child = relations.get_only_child_unit(unit.ident());

        let f = C::Field::with_string(String::from("child"), child.to_ctype_ptr());
        s.push_field(f);
    } else {
        unreachable!()
    }

    // add the struct to the scope and adding a typedef
    scope.push_struct(s);
    scope.new_typedef(&unit.to_type_name(), stype);
}

fn add_constructor_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // define the function
    let mut fun = C::Function::with_string(unit.constructor_fn_name(), C::Type::new_void());
    fun.set_static().set_inline();

    let unit_expr = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    // add the function parameter
    let params = if env.has_map_protect_unmap() {
        let mut params = Vec::new();
        if unit.maps_frame() {
            if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                let ty = unit.ptype_to_ctype(&etype.as_ref().into(), false);

                let param = fun.new_param("frame", ty).to_expr();
                params.push(("frame", param));
            } else {
                unimplemented!("expected a frame type!");
            }
        } else if unit.maps_table() {
            let child = relations.get_only_child_unit(unit.ident());

            let param = fun.new_param("child", child.to_ctype_ptr()).to_expr();
            params.push(("child", param));
        } else {
            unreachable!()
        }
        params
    } else {
        unit.params
            .iter()
            .map(|p| {
                let ty = unit.ptype_to_ctype(&p.ptype.typeinfo, false);
                let param = fun.new_param(p.ident().as_str(), ty).to_expr();
                (p.ident().as_str(), param)
            })
            .collect()
    };

    let body = fun.body();

    body.fn_call(
        "memset",
        vec![
            unit_expr.clone(),
            C::Expr::new_num(0),
            unit_expr.deref().size_of(),
        ],
    );

    // set the fields
    for (name, p) in params {
        body.assign(C::Expr::field_access(&unit_expr, name), p);
    }

    fun.push_doc_str("constructor of the unit type");

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Map/Unmap/Protect Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_op_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    op: &VelosiAstMethod,
    osspec: &VelosiAst,
    _has_children: bool,
) {
    let env = osspec.osspec().unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration
    // ---------------------------------------------------------------------------------------------

    let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
    fun.set_static().set_inline();
    fun.push_doc_str(&format!("Performs the {} operation on the unit", op));

    // ---------------------------------------------------------------------------------------------
    // Parameters
    // ---------------------------------------------------------------------------------------------

    let (mut param_vars, param_types) = add_fn_params(&mut fun, unit, op, osspec, false);

    // ---------------------------------------------------------------------------------------------
    // Body: Requires clauses
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();

    let mut vars = HashMap::new();
    // println!("{}", unit.to_op_fn_name(op));
    for (p, ty) in &param_types {
        // println!("p: {} -> {} extern: {}", p, ty, ty.is_extern());
        // print!("{} -> {} extern: {}", p, ty, ty.is_extern());
        if ty.is_extern() && *p == "pa" {
            let m = env.get_method_with_signature(&[ty.clone()], &VelosiAstTypeInfo::PhysAddr);
            if let Some(m) = m.first() {
                vars.insert(*p, C::Expr::fn_call(m.ident(), vec![param_vars[p].clone()]));
            } else {
                panic!("{} -> {}() var: {} {}", unit.ident(), op.ident(), p, ty);
            }
        } else if ty.is_typeref() && *p != "$unit" {
            if env.has_map_protect_unmap() {
                param_vars.insert(*p, param_vars[p].clone());
            } else {
                param_vars.insert(*p, C::Expr::field_access(&param_vars[p], "base"));
            }
            // here we have atype ref so we need something here
            // param_vars.insert(*p, C::Expr::field_access(&param_vars[p], "base"));

//            param_vars.insert(*p,  param_vars[p].clone()); //C::Expr::field_access(, "base22"));
  //          param_vars.insert(*p, )
        }
    }

    // if unit.ident().as_str() == "X8664PML4Entry" {
    //     println!("{:?}", vars);
    //     println!("-----");
    //     println!("{:?}", param_vars["pa"]);
    //     println!("-----");
    //     println!("{:?}", param_types);
    //     panic!("fofofo");
    // }

    // requires clauses
    for r in op.requires.iter() {
        // add asserts!
        body.new_comment(&format!("requires {}", r));
        body.new_ifelse(&C::Expr::lnot(unit.expr_to_cpp(&vars, r)))
            .then_branch()
            .return_expr(C::Expr::new_num(0));
    }

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    if env.has_map_protect_unmap() {
        //
        // we have an OS spec that we need to follow. We check whether the segment maps a frame
        // or another table. This is given by the type of the map function
        //
        let property = if unit.maps_frame() {
            VelosiAstTypeProperty::Frame
        } else if unit.maps_table() {
            VelosiAstTypeProperty::Descriptor
        } else {
            unreachable!()
        };

        // get the OSSpec method for the operation
        let method = if op.ident().as_str() == "map" {
            env.get_map_method(property).expect("map method not found?")
        } else {
            env.get_method(op.ident.as_str())
                .expect("didn't find the method")
        };

        // convert the body of the osspec operation into the struct, it will return true if
        // the operation has succeeded
        let spec_body = method
            .body
            .as_ref()
            .expect("map method didn't have a body?");

        let expr = if op.ident().as_str() == "map" {
            let pa = param_vars["pa"].clone();
            param_vars.insert("pa", param_vars["pa"].field_access("vnode"));
            let expr = unit.expr_to_cpp(&param_vars, spec_body);
            param_vars.insert("pa", pa);
            expr
        } else {
            unit.expr_to_cpp(&param_vars, spec_body)
        };

        // return the size if we mapped accordingly, otherwise return 0
        let ifelse = body.new_ifelse(&expr);

        if op.ident().as_str() == "map" {
            ifelse.then_branch().fn_call(
                &unit.set_child_fn_name(),
                vec![
                    param_vars["$unit"].clone(),
                    param_vars["va"].clone(),
                    param_vars["pa"].clone(),
                ],
            );
        }
        if op.ident().as_str() == "unmap" {
            ifelse.then_branch().fn_call(
                &unit.clear_child_fn_name(),
                vec![param_vars["$unit"].clone(), param_vars["va"].clone()],
            );
        }
        ifelse.then_branch().return_expr(param_vars["sz"].clone());
        ifelse.other_branch().return_expr(C::Expr::new_num(0));
    } else if !op.ops.is_empty() {
        //
        // we don't have an OS spec that defines the operation functions, instead we just
        // perform the mapping according to the operations.
        //
        // TODO: check this!
        //
        let mut fields = HashSet::new();
        for op in &op.ops {
            let fname = op.fieldname();
            if fname.is_empty() {
                continue;
            }
            fields.insert(String::from(fname));
        }
        body.new_comment("field variables");

        for field in &fields {
            if let Some(f) = unit.interface.field(field) {
                // get the field from the unit
                let field_type = f.to_type_name(unit);

                let var = body.new_variable(field, C::Type::new_typedef(&field_type));

                let fncall_name = f.to_set_val_fn(unit);
                var.set_value(C::Expr::fn_call(&fncall_name, vec![C::Expr::new_num(0)]));
                param_vars.insert(field.as_str(), var.to_expr());
            }
        }

        body.new_comment("configuration sequence");
        for op in &op.ops {
            utils::op_to_c_expr(unit.ident(), body, op, &param_vars);
        }

        body.return_expr(param_vars["sz"].clone());
    } else {
        body.new_comment("there is no configuration sequence");
        body.return_expr(C::Expr::new_num(0));
    }

    scope.push_function(fun);
}

fn add_do_map_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    has_children: bool,
) {
    let m_fn = unit.get_method("map").unwrap();
    add_op_fn(scope, unit, m_fn, osspec, has_children);
}

fn add_do_unmap_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    has_children: bool,
) {
    let m_fn = unit.get_method("unmap").unwrap();
    add_op_fn(scope, unit, m_fn, osspec, has_children);
}

fn add_do_protect_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    has_children: bool,
) {
    let m_fn = unit.get_method("protect").unwrap();
    add_op_fn(scope, unit, m_fn, osspec, has_children);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Utility functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_valid_fn(scope: &mut C::Scope, unit: &VelosiAstUnitSegment, osspec: &VelosiAst) {
    let env = osspec.osspec().unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration
    // ---------------------------------------------------------------------------------------------

    let mut fun = C::Function::with_string(unit.valid_fn_name(), C::Type::new_bool());
    fun.set_static().set_inline();
    fun.push_doc_str("Returns true if the mapping is valid");

    // ---------------------------------------------------------------------------------------------
    // Parameters
    // ---------------------------------------------------------------------------------------------

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    // ---------------------------------------------------------------------------------------------
    // Parameters
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();

    if env.has_map_protect_unmap() {
        // here we have a indirect way to set the things, we keep track of of the child pointer
        // in the function
        if unit.maps_frame() {
            if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                let m = env.get_method_with_signature(
                    &[VelosiAstTypeInfo::Extern(etype.ident.ident.clone())],
                    &VelosiAstTypeInfo::PhysAddr,
                );
                if m.is_empty() {
                    unimplemented!("should have some fn frame -> paddr defined");
                }
                let fname = m.first().unwrap().ident();
                body.return_expr(C::Expr::binop(
                    C::Expr::fn_call(fname, vec![C::Expr::field_access(&unit_param, "frame")]),
                    "!=",
                    C::Expr::new_num(0),
                ));
            } else {
                unreachable!();
            }
        } else if unit.maps_table() {
            body.return_expr(C::Expr::binop(
                C::Expr::field_access(&unit_param, "child"),
                "!=",
                C::Expr::null(),
            ));
        } else {
            unreachable!();
        }
    } else {
        let op = unit.methods.get("valid").expect("valid method not found!");
        let valid_body = op.body.as_ref().unwrap();

        let mut state_refs = HashSet::new();
        valid_body.get_state_references(&mut state_refs);

        let iface = &unit.interface;

        let mut vars = HashMap::new();
        vars.insert("$unit", unit_param.clone());

        let state = &unit.state;
        for sref in &state_refs {
            let val = iface
                .read_state_expr(sref, state.get_field_range(sref))
                .unwrap();

            let sref_var_name = format!("{}_val", sref.replace('.', "_"));

            let sref_var = body
                .new_variable(sref_var_name.as_str(), C::Type::new_uint64())
                .to_expr();

            body.assign(sref_var.clone(), unit.expr_to_cpp(&vars, &val));

            vars.insert(sref.as_str(), sref_var);
        }

        body.return_expr(unit.expr_to_cpp(&vars, valid_body));
    }

    scope.push_function(fun);
}

fn add_set_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // get the child unit
    let children = relations.get_children_units(unit.ident());

    if env.has_map_protect_unmap() {
        let fun = scope.new_function(unit.set_child_fn_name().as_str(), C::Type::new_void());
        fun.set_static().set_inline();
        fun.push_doc_str("Sets the child pointer of the unit");

        let unit_param = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
        let _va_param = fun
            .new_param(
                "va",
                unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
            )
            .to_expr();

        if unit.maps_frame() {
            if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                let child_param = fun
                    .new_param(
                        "dst",
                        unit.ptype_to_ctype(
                            &VelosiAstTypeInfo::Extern(etype.ident.ident.clone()),
                            false,
                        ),
                    )
                    .to_expr();
                fun.body()
                    .assign(unit_param.field_access("frame"), child_param);
            } else {
                unreachable!()
            }
        } else if unit.maps_table() {
            let rtype = match children.as_slice() {
                [] => C::Type::new_void(),
                [child] => child.to_ctype_ptr(),
                _ => unreachable!(),
            };

            let child_param = fun.new_param("dst", rtype).to_expr();

            fun.body()
                .assign(unit_param.field_access("child"), child_param);
        } else {
            unreachable!()
        }
    } else {
        scope.new_comment("No set-child function needed as no environment spec available.");
    }
}

fn add_clear_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    _relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();
    if env.has_map_protect_unmap() {
        let fun = scope.new_function(unit.clear_child_fn_name().as_str(), C::Type::new_void());
        fun.set_static().set_inline();
        fun.push_doc_str("Sets the child pointer of the unit");

        let unit_param = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
        let va_param = fun
            .new_param(
                "va",
                unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
            )
            .to_expr();

        if unit.maps_frame() {
            if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
                let v = C::Variable::new("frame", C::Type::new_typedef(etype.ident.ident()));
                let v_expr = v.to_expr();
                fun.body()
                    .variable(v)
                    .fn_call(
                        "memset",
                        vec![v_expr.addr_of(), C::Expr::new_num(0), v_expr.size_of()],
                    )
                    .fn_call(
                        unit.set_child_fn_name().as_str(),
                        vec![unit_param, va_param, v_expr],
                    );
            } else {
                unreachable!()
            }
        } else if unit.maps_table() {
            fun.body().fn_call(
                unit.set_child_fn_name().as_str(),
                vec![unit_param, va_param, C::Expr::null()],
            );
        } else {
            unreachable!();
        }
    }
}

fn add_get_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // get the child unit
    let children = relations.get_children_units(unit.ident());
    let child = match children.as_slice() {
        [] => return,
        [child] => child,
        _ => unreachable!(),
    };

    let rtype = if env.has_map_protect_unmap() {
        child.to_ctype_ptr()
    } else {
        child.to_ctype()
    };

    let fun = scope.new_function(unit.get_child_fn_name().as_str(), rtype);
    fun.set_static().set_inline();
    fun.push_doc_str("Gets the child pointer of the unit");

    // params

    let v_param_unit = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
    let _v_param_va = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();

    // body
    let body = fun.body();
    if env.has_map_protect_unmap() {
        body.return_expr(C::Expr::field_access(&v_param_unit, "child"));
    } else {
        body.fn_call(
            "assert",
            vec![C::Expr::fn_call(
                unit.valid_fn_name().as_str(),
                vec![v_param_unit.clone()],
            )],
        );

        body.new_comment("get the address of the next table by calling translate");
        let v_next_base = body
            .new_variable(
                "next_base",
                unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false),
            )
            .to_expr();
        body.assign(
            v_next_base.clone(),
            C::Expr::fn_call(
                &unit.translate_fn_name(),
                vec![v_param_unit, C::Expr::new_num(0)],
            ),
        );

        body.new_comment("construct the new unit");
        let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();
        body.fn_call(
            &child.constructor_fn_name(),
            vec![C::Expr::addr_of(&v_next_unit), v_next_base],
        );

        body.return_expr(v_next_unit);
    }
}

fn add_translate_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    _relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    if env.has_map_protect_unmap() {
        // nothing to be done here!
        return;
    }

    let translate_fn = unit.get_method("translate").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration
    // ---------------------------------------------------------------------------------------------

    let mut fun = C::Function::with_string(
        unit.translate_fn_name(),
        unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false),
    );
    fun.set_static().set_inline();
    fun.push_doc_str("Returns true if the mapping is valid");

    // ---------------------------------------------------------------------------------------------
    // Parameters
    // ---------------------------------------------------------------------------------------------

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    let va_param = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();

    let mut vars = HashMap::new();
    vars.insert("va", va_param.clone());
    vars.insert("$unit", unit_param.clone());

    // ---------------------------------------------------------------------------------------------
    // Function Body: Asserts
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();

    let translate_body = translate_fn.body.as_ref().unwrap();

    let mut state_refs: HashSet<Rc<String>> = HashSet::new();
    translate_body.get_state_references(&mut state_refs);

    for r in translate_fn.requires.iter() {
        let state_refs_new: HashSet<Rc<String>> = HashSet::new();
        r.get_state_references(&mut state_refs);
        state_refs.extend(state_refs_new)
    }

    for sref in &state_refs {
        if vars.contains_key(sref.as_str()) {
            continue;
        }
        let val = unit
            .interface
            .read_state_expr(sref, unit.state.get_field_range(sref))
            .unwrap();

        let sref_var_name = format!("{}_val", sref.replace('.', "_"));

        let sref_var = body
            .new_variable(sref_var_name.as_str(), C::Type::new_uint64())
            .to_expr();

        body.assign(sref_var.clone(), unit.expr_to_cpp(&vars, &val));

        vars.insert(sref, sref_var);
    }

    if translate_fn.requires.is_empty() {
        body.new_comment("no requires clauses");
    } else {
        body.new_comment("asserts for the requires clauses");
    }

    for r in translate_fn.requires.iter() {
        body.fn_call("assert", vec![unit.expr_to_cpp(&vars, r)]);
    }

    // adding an assert that the function should be valid
    body.fn_call(
        "assert",
        vec![C::Expr::fn_call(
            unit.valid_fn_name().as_str(),
            vec![unit_param.clone()],
        )],
    );

    // ---------------------------------------------------------------------------------------------
    // Function Body: Implementation
    // ---------------------------------------------------------------------------------------------

    body.return_expr(unit.expr_to_cpp(&vars, translate_body));

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Higher-Order Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn params_to_fn_arguments(
    op: &VelosiAstMethod,
    unit: C::Expr,
    params: &HashMap<&str, C::Expr>,
) -> Vec<C::Expr> {
    let mut args = vec![unit];
    args.extend(op.params.iter().map(|p| params[p.ident().as_str()].clone()));
    args
}

fn add_map_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    child: Option<&VelosiAstUnit>,
) {
    let m_fn = unit.get_method("map").unwrap();
    let env = osspec.osspec().unwrap();

    if unit.maps_table() && !(env.has_map_protect_unmap() || env.has_phys_alloc_fn()) {
        return;
    }

    // ---------------------------------------------------------------------------------------------
    // Function Declaration
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(m_fn).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    fun.push_doc_str(&format!("Higher-order {} function", m_fn.ident()));

    let (param_exprs, _) = add_fn_params(fun, unit, m_fn, osspec, true);

    let body = fun.body();

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let v_unit_param = param_exprs.get("$unit").unwrap();

    if let Some(child) = child {
        assert!(unit.maps_table());
        if env.has_map_protect_unmap() {
            let _map = env.get_map_method(VelosiAstTypeProperty::Frame);

            let cond = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![v_unit_param.clone()],
            )));

            let do_alloc_branch = cond.then_branch();
            do_alloc_branch.new_comment("Allocate the next-level structure");
            do_alloc_branch.fn_call(
                &child.to_allocate_fn_name(),
                vec![C::Expr::addr_of(&C::Expr::field_access(
                    v_unit_param,
                    "child",
                ))],
            );
            do_alloc_branch
                .new_ifelse(&C::Expr::binop(
                    C::Expr::field_access(v_unit_param, "child"),
                    "==",
                    C::Expr::null(),
                ))
                .then_branch()
                .return_expr(C::Expr::new_num(0x0));

            // let fun = scope.new_function(&unit.to_allocate_fn_name(), unit.to_ctype().to_ptr());

            cond.then_branch().new_comment("TODO: Map new child child");

            let alloc_cond = cond.then_branch().new_ifelse(&C::Expr::binop(
                C::Expr::fn_call(
                    unit.to_op_fn_name(m_fn).as_str(),
                    vec![
                        v_unit_param.clone(),
                        C::Expr::new_num(0), // va is always 0 here
                        C::Expr::new_num(1 << child.input_bitwidth()), // sz: set the size properly or set it to 0
                        C::Expr::new_var("DEFAULT_FLAGS", C::Type::new_void()), // TODO: set flags to allow everything
                        C::Expr::field_access(v_unit_param, "child"),
                    ],
                ),
                "==",
                C::Expr::new_num(0),
            ));

            alloc_cond.then_branch().return_expr(C::Expr::new_num(0));

            let mut args = vec![C::Expr::field_access(v_unit_param, "child")];

            for f in m_fn.params.iter() {
                let p = if f.ident().as_str() == "pa" {
                    if let Some(ty) =
                        env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame)
                    {
                        C::Type::new_typedef(ty.ident.as_str())
                    } else {
                        unit.ptype_to_ctype(&f.ptype.typeinfo, false)
                    }
                } else {
                    unit.ptype_to_ctype(&f.ptype.typeinfo, false)
                };
                args.push(C::Expr::new_var(f.ident.as_str(), p))
            }

            body.return_expr(C::Expr::fn_call(&child.to_hl_op_fn_name(m_fn), args));
        } else {
            let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();

            // if entry.valid() { }
            let valid_check = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![param_exprs["$unit"].clone()],
            )));
            valid_check
                .then_branch()
                .new_comment("Allocate the next-level structure")
                .fn_call(
                    &child.to_allocate_fn_name(),
                    vec![C::Expr::addr_of(&v_next_unit)],
                )
                .new_comment("TODO: Check whether allocation has succeeded!")
                .fn_call(
                    &unit.to_op_fn_name(m_fn),
                    vec![
                        v_unit_param.clone(),                                               // unit ptr
                        C::Expr::new_num(0), // VA: should be 0
                        C::Expr::new_num(1 << child.input_bitwidth()), // sz
                        C::Expr::new_var("DEFAULT_FLAGS", C::Type::new_typedef("flags_t")), // just all flags for now
                        C::Expr::addr_of(&v_next_unit), // the destination pointer
                    ],
                );
            // else {}
            valid_check.other_branch().assign(
                v_next_unit.clone(),
                C::Expr::fn_call(
                    &unit.get_child_fn_name(),
                    vec![
                        v_unit_param.clone(), // unit ptr
                        C::Expr::new_num(0),  // VA: should be 0
                    ],
                ),
            );

            // now we can recurse
            body.return_expr(C::Expr::fn_call(
                &child.to_hl_op_fn_name(m_fn),
                params_to_fn_arguments(m_fn, C::Expr::addr_of(&v_next_unit), &param_exprs),
            ));
        }
    } else {
        // This is a mapping of a frame, so we create the mapping here and are good with it
        assert!(!unit.maps_table());

        if env.has_map_protect_unmap() {
            let _map = env.get_map_method(VelosiAstTypeProperty::Frame);

            let cond = body.new_ifelse(&C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![v_unit_param.clone()],
            ));
            cond.then_branch().return_expr(C::Expr::new_num(0));

            let mut args = vec![param_exprs["$unit"].clone()];
            args.extend(
                m_fn.params
                    .iter()
                    .map(|p| param_exprs.get(p.ident().as_str()).unwrap())
                    .cloned(),
            );

            body.return_expr(C::Expr::fn_call(&unit.to_op_fn_name(m_fn), args));
        } else {
            body.new_comment("this is just calling the operation on the unit directy");

            let mut args = vec![param_exprs["$unit"].clone()];
            args.extend(
                m_fn.params
                    .iter()
                    .map(|p| param_exprs.get(p.ident().as_str()).unwrap())
                    .cloned(),
            );
            body.return_expr(C::Expr::fn_call(&unit.to_op_fn_name(m_fn), args));
        }
    }
}

fn add_unmap_protect_function_common(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    m_fn: &VelosiAstMethod,
    osspec: &VelosiAst,
    child: Option<&VelosiAstUnit>,
) {
    // ---------------------------------------------------------------------------------------------
    // Function Declaration
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(m_fn).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    fun.push_doc_str(&format!("Higher-order {} function", m_fn.ident()));

    let (param_exprs, _) = add_fn_params(fun, unit, m_fn, osspec, true);

    let env = osspec.osspec().unwrap();
    let body = fun.body();

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let v_unit_param = param_exprs.get("$unit").unwrap();

    if let Some(child) = child {
        assert!(unit.maps_table());

        if env.has_map_protect_unmap() {
            let cond = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![v_unit_param.clone()],
            )));

            cond.then_branch().return_expr(C::Expr::new_num(0));

            // now we can recurse
            let v_next_unit = body
                .new_variable("next_unit", child.to_ctype_ptr())
                .to_expr();
            body.assign(
                v_next_unit.clone(),
                C::Expr::fn_call(
                    &unit.get_child_fn_name(),
                    vec![
                        v_unit_param.clone(), // unit ptr
                        C::Expr::new_num(0),  // VA: should be 0
                    ],
                ),
            );

            body.return_expr(C::Expr::fn_call(
                &child.to_hl_op_fn_name(m_fn),
                params_to_fn_arguments(m_fn, v_next_unit, &param_exprs),
            ));
        } else {
            let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();

            let valid_check = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![param_exprs["$unit"].clone()],
            )));
            valid_check.then_branch().return_expr(C::Expr::new_num(0));

            // now we can recurse
            body.assign(
                v_next_unit.clone(),
                C::Expr::fn_call(
                    &unit.get_child_fn_name(),
                    vec![
                        v_unit_param.clone(), // unit ptr
                        C::Expr::new_num(0),  // VA: should be 0
                    ],
                ),
            )
            .return_expr(C::Expr::fn_call(
                &child.to_hl_op_fn_name(m_fn),
                params_to_fn_arguments(m_fn, C::Expr::addr_of(&v_next_unit), &param_exprs),
            ));
        }
    } else {
        assert!(!unit.maps_table());

        if env.has_map_protect_unmap() {
            body.new_comment("TODO: Implement me!");

            let cond = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
                &unit.valid_fn_name(),
                vec![v_unit_param.clone()],
            )));

            let mut args = vec![param_exprs["$unit"].clone()];
            args.extend(
                m_fn.params
                    .iter()
                    .map(|p| param_exprs.get(p.ident().as_str()).unwrap())
                    .cloned(),
            );

            if m_fn.ident().as_str() == "unmap" {
                cond.then_branch().return_expr(param_exprs["sz"].clone());
                cond.other_branch()
                    .return_expr(C::Expr::fn_call(&unit.to_op_fn_name(m_fn), args));
            } else if m_fn.ident().as_str() == "protect" {
                cond.then_branch().return_expr(C::Expr::new_num(0));
                cond.other_branch()
                    .return_expr(C::Expr::fn_call(&unit.to_op_fn_name(m_fn), args));
            }
        } else {
            body.new_comment("this is just calling the operation on the unit directy");

            let mut args = vec![param_exprs["$unit"].clone()];
            args.extend(
                m_fn.params
                    .iter()
                    .map(|p| param_exprs.get(p.ident().as_str()).unwrap())
                    .cloned(),
            );

            body.return_expr(C::Expr::fn_call(&unit.to_op_fn_name(m_fn), args));
        }
    }
}

fn add_unmap_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    child: Option<&VelosiAstUnit>,
) {
    let m_fn = unit.get_method("unmap").unwrap();
    add_unmap_protect_function_common(scope, unit, m_fn, osspec, child);
}

fn add_protect_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    child: Option<&VelosiAstUnit>,
) {
    let m_fn = unit.get_method("protect").unwrap();
    add_unmap_protect_function_common(scope, unit, m_fn, osspec, child);
}

fn add_resolve_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    osspec: &VelosiAst,
    child: Option<&VelosiAstUnit>,
) {
    let env = osspec.osspec().unwrap();

    let rtype = if let Some(ty) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
        C::Type::new_typedef(ty.ident.as_str()).to_ptr()
    } else {
        unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false)
    };

    //
    let mut fun = C::Function::with_string(unit.resolve_fn_name(), C::Type::new_bool());
    fun.set_static().set_inline();

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    let vaddr_param = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();

    let paddr_param = fun.new_param("pa", rtype.to_ptr()).to_expr();

    // ---------------------------------------------------------------------------------------------
    // Function Body: Implementation
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();

    let cond = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
        &unit.valid_fn_name(),
        vec![unit_param.clone()],
    )));
    cond.then_branch().return_expr(C::Expr::bfalse());

    if let Some(child) = child {
        assert!(unit.maps_table());
        if env.has_map_protect_unmap() {
            body.return_expr(C::Expr::fn_call(
                &child.resolve_fn_name(),
                vec![
                    C::Expr::field_access(&unit_param, "child"),
                    vaddr_param,
                    paddr_param.clone(),
                ],
            ));
        } else {
            let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();
            body.assign(
                v_next_unit.clone(),
                C::Expr::fn_call(
                    &unit.get_child_fn_name(),
                    vec![
                        unit_param.clone(),  // unit ptr
                        C::Expr::new_num(0), // VA: should be 0
                    ],
                ),
            )
            .return_expr(C::Expr::fn_call(
                &unit.resolve_fn_name(),
                vec![unit_param, vaddr_param, paddr_param],
            ));
        }
    } else {
        assert!(unit.maps_frame());
        // no child here, so we're directly doing the thing here!
        if env.has_map_protect_unmap() {
            body.assign(
                C::Expr::deref(&paddr_param),
                unit_param.field_access("frame").addr_of(),
            )
            .return_expr(C::Expr::btrue());
        } else {
            body.assign(
                C::Expr::deref(&paddr_param),
                C::Expr::fn_call(&unit.translate_fn_name(), vec![unit_param, vaddr_param]),
            )
            .return_expr(C::Expr::btrue());
        }
    }

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allocate / Free Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_free_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return;
    }

    let env = osspec.osspec().unwrap();

    let ptype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr()
    } else {
        unit.to_ctype()
    };

    let fun = scope.new_function(&unit.to_free_fn_name(), C::Type::new_void());
    let _unit_param = fun.new_param("unit", ptype).to_expr();
}

fn add_allocate_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return;
    }

    let env = osspec.osspec().unwrap();

    let rtype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr()
    } else {
        unit.to_ctype()
    };

    let _fun = scope.new_function(&unit.to_allocate_fn_name(), rtype);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allocate / Free Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// generates the VelosiAstUnitSegment definitions
pub fn generate(
    unit: &VelosiAstUnitSegment,
    relations: &Relations,
    osspec: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating segment unit {}", unit.ident());

    let env = osspec.osspec().unwrap();

    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("Unit Definitions for `{}`", unit.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_UNIT_H_", unit.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Includes
    ////////////////////////////////////////////////////////////////////////////////////////////////

    // add the header comments
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);
    s.new_include("string.h", true);

    // adding the OS spec header here
    s.new_include(&format!("{}.h", env.ident().to_lowercase()), true);

    // adding includes for each of the children
    for child in relations.get_children(unit.ident()) {
        s.new_include(&format!("{}_unit.h", child.to_lowercase()), false);
    }

    // the interface and global constants
    if !env.has_map_protect_unmap() {
        s.new_include(
            &format!("{}_interface.h", unit.ident().to_lowercase()),
            false,
        );
    }

    s.new_include("consts.h", false);
    s.new_include("types.h", false);

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Unit Constants and Constructor
    ////////////////////////////////////////////////////////////////////////////////////////////////

    s.new_comment(" --------------------------- Constants / Constructor -------------------------");

    add_unit_constants(s, unit);
    add_unit_struct(s, unit, relations, osspec);
    add_constructor_function(s, unit, relations, osspec);

    s.new_comment(" ----------------------------- Allocate and free ----------------------------");

    add_allocate_function(s, unit, relations, osspec);
    add_free_function(s, unit, relations, osspec);

    s.new_comment(" ----------------------------- Address Translation  --------------------------");

    add_valid_fn(s, unit, osspec);
    add_translate_fn(s, unit, relations, osspec);

    add_set_child_fn(s, unit, relations, osspec);
    add_clear_child_fn(s, unit, relations, osspec);
    add_get_child_fn(s, unit, relations, osspec);

    s.new_comment(" ---------------------------- Map / Protect/ Unmap ---------------------------");

    let mut children = relations.get_children_units(unit.ident());
    debug_assert!(children.len() <= 1);

    let child = children.pop();
    let has_children = child.is_some();

    add_do_map_function(s, unit, osspec, has_children);
    add_do_unmap_function(s, unit, osspec, has_children);
    add_do_protect_function(s, unit, osspec, has_children);

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Other Functions
    ////////////////////////////////////////////////////////////////////////////////////////////////

    s.new_comment(" --------------------------- Higher Order Functions --------------------------");

    add_map_function(s, unit, osspec, child.as_ref());
    add_protect_function(s, unit, osspec, child.as_ref());
    add_unmap_function(s, unit, osspec, child.as_ref());

    add_resolve_function(s, unit, osspec, child.as_ref());

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Saving the file
    ////////////////////////////////////////////////////////////////////////////////////////////////

    log::debug!("saving the scope!");
    // save the scope

    let filename = format!("{}_unit.h", unit.ident().to_ascii_lowercase());

    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;

    Ok(())
}
