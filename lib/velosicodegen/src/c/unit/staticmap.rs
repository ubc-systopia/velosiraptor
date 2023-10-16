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

//! StaticMap Generation (C)

use std::path::Path;
use std::{collections::HashMap, rc::Rc};

use crustal as C;

use velosiast::{
    VelosiAst, VelosiAstMethod, VelosiAstStaticMap, VelosiAstStaticMapExplicit,
    VelosiAstStaticMapListComp, VelosiAstTypeInfo, VelosiAstTypeProperty, VelosiAstUnit,
    VelosiAstUnitProperty, VelosiAstUnitSegment, VelosiAstUnitStaticMap,
};
use velosicomposition::Relations;

use super::utils::{self, UnitUtils};
use crate::VelosiCodeGenError;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constants
////////////////////////////////////////////////////////////////////////////////////////////////////

/// adds the constants defined in the unit to the scope
fn add_unit_constants(scope: &mut C::Scope, unit: &VelosiAstUnitStaticMap) {
    scope.new_comment("Defined unit constants");
    if unit.consts.is_empty() {
        scope.new_comment("The unit does not define any constants");
        return;
    }

    // now add the constants
    for c in unit.consts.values() {
        utils::add_const_def(scope, c);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constructors
////////////////////////////////////////////////////////////////////////////////////////////////////

fn next_unit_type(
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) -> C::Type {
    let env = osspec.osspec().unwrap();

    let root_units = relations.get_roots();

    match relations.get_children_units(unit.ident()).as_slice() {
        [VelosiAstUnit::Enum(e)] => {
            if env.has_map_protect_unmap() {
                C::Type::new_typedef(&unit.to_child_type_name())
            } else {
                e.as_ref().to_ctype()
            }
        }
        [VelosiAstUnit::Segment(e)] => {
            if env.has_map_protect_unmap() {
                C::Type::new_typedef(&unit.to_child_type_name())
            } else {
                e.as_ref().to_ctype()
            }
        }
        _ => unreachable!(),
    }
}

fn generate_child_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // if we have a spec, then we don't need to generate this as we can use the child directly
    if !env.has_map_protect_unmap() {
        return;
    }

    let mut children_struct = C::Struct::new(&unit.to_child_struct_name());
    let children_struct_ty = children_struct.to_type();

    match &unit.map {
        VelosiAstStaticMap::ListComp(lc) => {
            if lc.is_repr_list() {
                children_struct.push_doc_str("list element");
                children_struct
                    .new_field("next", C::Type::new_typedef_ptr(&unit.to_child_type_name()));
                children_struct.new_field(
                    "va",
                    unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
                );
            } else {
                children_struct.push_doc_str("array element");
            }
        }
        _ => unimplemented!("handling of other map types"),
    };

    match relations.get_children_units(unit.ident()).as_slice() {
        [VelosiAstUnit::Enum(e)] => {
            let children = relations.get_children_units(e.ident());

            let roots = relations.get_group_roots();

            let mut children_union = C::Union::new(&unit.to_child_union_name());
            let mut children_enum = C::Enum::new(&unit.to_child_kind_name());

            for child in &children {
                if let VelosiAstUnit::Segment(s) = child {
                    if s.maps_frame() {
                        // here we map a frame
                        let mut child_struct = C::Struct::new(&child.to_struct_name());
                        if let Some(frametype) =
                            env.get_extern_type_with_property(VelosiAstTypeProperty::Frame)
                        {
                            child_struct
                                .new_field("frame", C::Type::new_typedef(frametype.ident.as_str()));
                        } else {
                            child_struct.new_field("dummy", C::Type::new_int32());
                        }

                        let child_ty = child_struct.to_type();

                        scope.push_struct(child_struct);
                        scope.new_typedef(&child.to_type_name(), child_ty);

                        children_union.new_field(
                            &child.ident().to_ascii_lowercase(),
                            C::Type::new_typedef(&child.to_type_name()),
                        );
                    } else if s.maps_table() {
                        // if the next one is a table, then that should already have been defined
                        let next = relations.get_only_child_unit(s.ident());
                        children_union
                            .new_field(&child.ident().to_ascii_lowercase(), next.to_ctype());
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!("should always be a segment here");
                }

                children_enum.new_variant(&child.ident().to_ascii_uppercase());
            }
            let children_enum_ty = children_enum.to_type();
            let children_union_ty = children_union.to_type();
            scope.push_enum(children_enum);
            scope.push_union(children_union);
            children_struct.new_field("kind", children_enum_ty);
            children_struct.new_field("variants", children_union_ty);
        }
        [VelosiAstUnit::Segment(e)] => {}
        _ => unreachable!(),
    }

    scope
        .push_struct(children_struct)
        .new_typedef(&unit.to_child_type_name(), children_struct_ty);
}

fn generate_unit_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    generate_child_struct(scope, unit, relations, osspec);

    let children = relations.get_children_units(unit.ident());
    assert!(children.len() == 1);
    let child = &children[0];

    let child_type = next_unit_type(unit, relations, osspec);

    let env = osspec.osspec().unwrap();

    let mut fields = if env.has_map_protect_unmap() {
        let mut fields = Vec::new();
        for etype in env.extern_types.values() {
            if etype
                .properties
                .contains(&VelosiAstTypeProperty::Descriptor)
            {
                for field in &etype.fields {
                    fields.push(C::Field::with_string(
                        field.ident_to_string(),
                        unit.ptype_to_ctype(&field.ptype.typeinfo, false),
                    ));
                }
                break;
            }
        }

        let properties = unit.properties();
        if properties.contains(&VelosiAstUnitProperty::ArrayRepr) {
            // array representation
            fields.push(C::Field::with_string(
                "child".to_string(),
                child_type.to_ptr().to_array(unit.map_size()),
            ));
        } else if properties.contains(&VelosiAstUnitProperty::ListRepr) {
            fields.push(C::Field::with_string(
                "child".to_string(),
                child_type.to_ptr(),
            ));
        } else {
            fields.push(C::Field::with_string(
                "child".to_string(),
                child_type.to_ptr(),
            ));
        }

        fields
    } else {
        unit.params
            .iter()
            .map(|x| C::Field::with_string(x.ident().to_string(), C::Type::new_uintptr()))
            .collect()
    };

    let mut s = C::Struct::with_fields(&unit.to_struct_name(), fields);
    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

    let stype = s.to_type();

    match &unit.map {
        VelosiAstStaticMap::ListComp(lc) => {
            if lc.is_repr_list() {
                s.push_doc_str("list element");
                s.new_field("next", stype.to_ptr());
            }
        }
        _ => unimplemented!("handling of other map types"),
    };

    // add the struct definition to the scope
    scope.push_struct(s);

    // add the type def to the scope
    scope.new_typedef(&unit.to_type_name(), stype);
}

fn add_constructor_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let mut fun = C::Function::with_string(unit.constructor_fn_name(), C::Type::new_void());
    fun.set_static().set_inline();

    let unit_expr = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();

    // add the function parameter
    let params = if env.has_map_protect_unmap() {
        let mut params = Vec::new();
        for etype in env.extern_types.values() {
            if etype
                .properties
                .contains(&VelosiAstTypeProperty::Descriptor)
            {
                for field in &etype.fields {
                    let ty = unit.ptype_to_ctype(&field.ptype.typeinfo, true);
                    let param = fun.new_param(field.ident(), ty).to_expr();
                    params.push((field.ident(), param));
                }
                break;
            }
        }
        params
    } else {
        unit.params
            .iter()
            .map(|p| {
                let ty = unit.ptype_to_ctype(&p.ptype.typeinfo, false);
                let param = fun.new_param(p.ident(), ty).to_expr();
                (p.ident(), param)
            })
            .collect()
    };

    let body = fun.body();

    for (name, p) in params {
        body.assign(C::Expr::field_access(&unit_expr, name), p);
    }

    if env.has_map_protect_unmap() {
        body.fn_call(
            "memset",
            vec![
                C::Expr::field_access(&unit_expr, "child"),
                C::Expr::new_num(0),
                C::Expr::size_of(&C::Expr::field_access(&unit_expr, "child")),
            ],
        );
    }

    fun.push_doc_str("constructor of the unit type");

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Map/Unmap/Protect Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_fn_params<'a>(
    fun: &mut C::Function,
    unit: &VelosiAstUnitStaticMap,
    op: &'a VelosiAstMethod,
    osspec: &VelosiAst,
) -> HashMap<&'a str, C::Expr> {
    let env = osspec.osspec().unwrap();

    let mut param_exprs = HashMap::new();

    let unit_param = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("$unit", unit_param.clone());

    for f in op.params.iter() {
        let p = if f.ident().as_str() == "pa" {
            if let Some(ty) = env.get_extern_type_with_property(VelosiAstTypeProperty::Frame) {
                fun.new_param(f.ident(), C::Type::new_typedef(ty.ident.as_str()))
            } else {
                fun.new_param(
                    f.ident(),
                    unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, true),
                )
            }
        } else {
            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true))
        };

        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    param_exprs
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Map/Unmap/Protect Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_do_op_fn_body_listcomp(
    scope: &mut C::Block,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
    variant_unit: Option<&VelosiAstUnit>,
    mut params_exprs: HashMap<&str, C::Expr>,
) {
    scope.new_comment(map.to_string().as_str());

    let idx_var = scope.new_variable("idx", C::Type::new_size()).to_expr();

    let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
    let va_var = params_exprs.get("va").unwrap();

    // idx = va / element_size
    scope.assign(
        idx_var.clone(),
        C::Expr::binop(
            va_var.clone(),
            ">>",
            C::Expr::ConstNum(dest_unit.input_bitwidth()),
        ),
    );

    // va = va & (element_size - 1)
    scope.assign(
        va_var.clone(),
        C::Expr::binop(
            va_var.clone(),
            "&",
            C::Expr::binop(
                C::Expr::binop(
                    C::Expr::ConstNum(1),
                    "<<",
                    C::Expr::ConstNum(dest_unit.input_bitwidth()),
                ),
                "-",
                C::Expr::ConstNum(1),
            ),
        ),
    );

    // nee d

    let tunit = scope
        .new_variable("targetunit", dest_unit.to_ctype())
        .to_expr();

    let unit_var = params_exprs.get("unit").unwrap();
    let mut var_mappings = HashMap::new();
    for p in unit.params_as_slice() {
        var_mappings.insert(
            p.ident().as_str(),
            C::Expr::field_access(unit_var, p.ident().as_str()),
        );
    }

    var_mappings.insert(map.var.ident().as_str(), idx_var);

    // TODO here!
    let args = map
        .elm
        .dst
        .args
        .iter()
        .map(|p| unit.expr_to_cpp(&var_mappings, p))
        .collect();

    scope.assign(
        tunit.clone(),
        C::Expr::fn_call(&dest_unit.constructor_fn_name(), args),
    );

    let mut args = vec![C::Expr::addr_of(&tunit)];
    for arg in op.params.iter() {
        let e = params_exprs.remove(arg.ident().as_str()).unwrap();
        args.push(e);
    }
    let fn_name = match variant_unit {
        Some(variant_unit) => dest_unit.to_op_fn_name_on_unit(op, variant_unit),
        None => dest_unit.to_op_fn_name(op),
    };

    scope.return_expr(C::Expr::fn_call(&fn_name, args));
}

fn add_op_fnunction(
    scope: &mut C::Scope,
    ast: &VelosiAst,
    unit: &VelosiAstUnitStaticMap,
    op_name: &str,
) {
    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: explicit map
        }
        VelosiAstStaticMap::ListComp(map) => {
            let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
            match dest_unit {
                VelosiAstUnit::Enum(e) if op_name == "map" => {
                    for variant in e.get_next_unit_idents() {
                        let variant_unit = ast.get_unit(variant).unwrap();
                        let op = variant_unit.get_method(op_name).unwrap();

                        // declare the function
                        let mut fun = C::Function::with_string(
                            unit.to_op_fn_name_on_unit(op, variant_unit),
                            C::Type::new_size(),
                        );
                        fun.set_static().set_inline();

                        let mut param_exprs = HashMap::new();

                        let v = fun
                            .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                            .to_expr();
                        param_exprs.insert("unit", v);
                        for f in op.params.iter() {
                            let p = fun
                                .new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
                            param_exprs.insert(f.ident().as_str(), p.to_expr());
                        }

                        // todo: add requires

                        add_do_op_fn_body_listcomp(
                            fun.body(),
                            ast,
                            unit,
                            map,
                            op,
                            Some(variant_unit),
                            param_exprs,
                        );

                        // push the function to the scope
                        scope.push_function(fun);
                    }
                }
                _ => {
                    let op = if dest_unit.is_enum() {
                        unit.get_method(op_name).unwrap()
                    } else {
                        dest_unit.get_method(op_name).unwrap()
                    };
                    let fn_name = if op_name == "map" {
                        unit.to_op_fn_name_on_unit(op, dest_unit)
                    } else {
                        unit.to_op_fn_name_one(op)
                    };

                    // declare the function
                    let mut fun = C::Function::with_string(fn_name, C::Type::new_size());
                    fun.set_static().set_inline();

                    let mut param_exprs = HashMap::new();

                    let v = fun
                        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                        .to_expr();
                    param_exprs.insert("unit", v);
                    for f in op.params.iter() {
                        let p =
                            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
                        param_exprs.insert(f.ident().as_str(), p.to_expr());
                    }

                    // todo: add requires

                    add_do_op_fn_body_listcomp(fun.body(), ast, unit, map, op, None, param_exprs);

                    // push the function to the scope
                    scope.push_function(fun);
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // no map defined
        }
    }
}

fn add_op_fn_list_comp(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    child: &VelosiAstUnit,
    map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
    _relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
    fun.set_static().set_inline();
    fun.push_doc_str(&format!("Performs the {} operation on the unit", op));

    let mut param_exprs = HashMap::new();
    let v = fun
        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
        .to_expr();
    param_exprs.insert("$unit", v);
    for f in op.params.iter() {
        let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
        param_exprs.insert(f.ident().as_str(), p.to_expr());
    }

    if map.elm.src.is_some() {
        unimplemented!()
    } else if let VelosiAstUnit::Enum(_child) = child {
        // here we need to differentiate and do something with the given enum variants
        // so we can call the map functions accordingly!
    } else if let VelosiAstUnit::Segment(child) = child {
        if child.maps_frame() {
        } else if child.maps_table() {
        } else {
            unreachable!()
        }
        // this is the easy case, we just have normal segments and we can basically just do the
        // mapping here depending on whether the child is a frame or table mapping
        if env.has_map_protect_unmap() {}
    } else {
        unreachable!()
    }

    scope.push_function(fun);
}

//
// do_map_table(pdir, va, sz, flgs, ptable)
// do_map_frame(pdir, va, sz, flags, frame)
//
//
// map(pdir, va, sz, flgs, frame) {
//  while cur < sz {
//       if can_map
//  }
//   if can_map_large(pdir, va, sz, flags) {
//      return
//   } else {
//
//   }
// }

fn add_op_fn_explicit(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitStaticMap,
    _child: &VelosiAstUnit,
    _map: &VelosiAstStaticMapExplicit,
    _op: &VelosiAstMethod,
    _osspec: &VelosiAst,
) {
    unimplemented!()
}

fn add_op_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    child: &VelosiAstUnit,
    op: &VelosiAstMethod,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    match &unit.map {
        VelosiAstStaticMap::Explicit(map) => {
            add_op_fn_explicit(scope, unit, child, map, op, osspec);
        }
        VelosiAstStaticMap::ListComp(map) => {
            add_op_fn_list_comp(scope, unit, child, map, op, relations, osspec);
        }
        VelosiAstStaticMap::None(_) => {
            unreachable!();
        }
    }
}

fn add_do_map_function(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitStaticMap,
    _relations: &Relations,
    _osspec: &VelosiAst,
) {
    // let m_fn = unit.get_method("map").unwrap();
    // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
}

fn add_do_unmap_function(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitStaticMap,
    _relations: &Relations,
    _osspec: &VelosiAst,
) {
    // let m_fn = unit.get_method("unmap").unwrap();
    // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
}

fn add_do_protect_function(
    _scope: &mut C::Scope,
    _unit: &VelosiAstUnitStaticMap,
    _relations: &Relations,
    _osspec: &VelosiAst,
) {
    // let m_fn = unit.get_method("protect").unwrap();
    // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Utility functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn base_inbitwidth(relations: &Relations, ident: &Rc<String>, inbitwidth: u64) -> u64 {
    let children = relations.get_children_units(ident);
    if children.is_empty() {
        inbitwidth
    } else {
        children
            .iter()
            .map(|u| base_inbitwidth(relations, u.ident(), u.input_bitwidth()))
            .chain(std::iter::once(inbitwidth))
            .min()
            .unwrap()
    }
}

fn add_higher_order_map(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    _osspec: &VelosiAst,
) {
    let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(map) => {
            let dest_unit = &relations.get_children_units(unit.ident())[0];
            match dest_unit {
                VelosiAstUnit::Enum(e) => {
                    let op = unit.get_method("map").unwrap();

                    let mut fun =
                        C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
                    fun.set_static().set_inline();

                    let mut param_exprs = HashMap::new();

                    let v = fun
                        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                        .to_expr();
                    param_exprs.insert("unit", v.clone());
                    for f in op.params.iter() {
                        let p =
                            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
                        param_exprs.insert(f.ident().as_str(), p.to_expr());
                    }

                    let va = &param_exprs["va"];
                    let sz = &param_exprs["sz"];
                    let pa = &param_exprs["pa"];
                    let body = &mut fun.body();

                    // add assertions
                    for arg in [va, sz, pa] {
                        body.fn_call(
                            "assert",
                            vec![C::Expr::binop(
                                C::Expr::binop(
                                    arg.clone(),
                                    "%",
                                    C::Expr::new_num(base_page_size as u64),
                                ),
                                "==",
                                C::Expr::new_num(0),
                            )],
                        );
                    }

                    let original_sz = body
                        .new_variable("original_sz", C::Type::new_size())
                        .to_expr();
                    body.assign(original_sz.clone(), sz.clone());

                    let (has_children, no_children): (Vec<_>, Vec<_>) = e
                        .get_next_unit_idents()
                        .into_iter()
                        .partition(|variant| !relations.get_children(variant).is_empty());

                    for variant in no_children {
                        let variant_unit = relations.get_unit(variant).unwrap();
                        let page_size: usize = 1 << variant_unit.input_bitwidth();

                        let mut if_block = C::IfElse::new(&C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(
                                    C::Expr::binop(
                                        va.clone(),
                                        "%",
                                        C::Expr::new_num(page_size as u64),
                                    ),
                                    "==",
                                    C::Expr::new_num(0),
                                ),
                                "&&",
                                C::Expr::binop(
                                    C::Expr::binop(
                                        pa.clone(),
                                        "%",
                                        C::Expr::new_num(page_size as u64),
                                    ),
                                    "==",
                                    C::Expr::new_num(0),
                                ),
                            ),
                            "&&",
                            C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                        ));
                        let i = if_block
                            .then_branch()
                            .new_variable("i", C::Type::new_size())
                            .to_expr();
                        if_block.then_branch().assign(
                            i.clone(),
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(variant_unit.input_bitwidth()),
                            ),
                        );

                        let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(
                                    va.clone(),
                                    ">>",
                                    C::Expr::new_num(variant_unit.input_bitwidth()),
                                ),
                                "==",
                                i,
                            ),
                            "&&",
                            C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                        ));

                        let mut args = Vec::new();
                        for arg in op.params.iter() {
                            if arg.ident().as_str() == "sz" {
                                args.push(C::Expr::new_num(page_size as u64))
                            } else {
                                let e = param_exprs[arg.ident().as_str()].clone();
                                args.push(e);
                            }
                        }

                        while_block
                            .body()
                            .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);
                        while_block.body().assign(
                            sz.clone(),
                            C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
                        );
                        while_block.body().assign(
                            va.clone(),
                            C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
                        );
                        while_block.body().assign(
                            pa.clone(),
                            C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
                        );

                        if_block.then_branch().while_loop(while_block);
                        body.ifelse(if_block);
                    }

                    for variant in &has_children {
                        let children = relations.get_children_units(variant);
                        let child = &children[0];
                        let variant_unit = relations.get_unit(variant).unwrap();

                        let i = body.new_variable("i", C::Type::new_size()).to_expr();
                        body.assign(
                            i.clone(),
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(variant_unit.input_bitwidth()),
                            ),
                        );

                        let tunit = body
                            .new_variable("targetunit", (&dest_unit).to_ctype())
                            .to_expr();

                        let unit_var = param_exprs.get("unit").unwrap();
                        let mut var_mappings = HashMap::new();
                        for p in unit.params_as_slice() {
                            var_mappings.insert(
                                p.ident().as_str(),
                                C::Expr::field_access(unit_var, p.ident().as_str()),
                            );
                        }

                        var_mappings.insert(map.var.ident().as_str(), i);

                        let args = map
                            .elm
                            .dst
                            .args
                            .iter()
                            .map(|p| unit.expr_to_cpp(&var_mappings, p))
                            .collect();

                        body.assign(
                            tunit.clone(),
                            C::Expr::fn_call(&(&dest_unit).constructor_fn_name(), args),
                        );

                        let mut if_block = C::IfElse::new(&C::Expr::uop(
                            "!",
                            C::Expr::fn_call(&(&dest_unit).valid_fn_name(), vec![tunit.clone()]),
                        ));
                        let child_paddr = if_block
                            .then_branch()
                            .new_variable("child_paddr", C::Type::new_typedef("paddr_t"))
                            .to_expr();
                        if_block.then_branch().assign(
                            child_paddr.clone(),
                            C::Expr::fn_call(
                                "virt_to_phys",
                                vec![C::Expr::fn_call(
                                    "alloc",
                                    vec![C::Expr::new_num(base_page_size as u64)],
                                )],
                            ),
                        );
                        let child_var = if_block
                            .then_branch()
                            .new_variable("child", child.to_ctype())
                            .to_expr();
                        if_block.then_branch().assign(
                            child_var.clone(),
                            C::Expr::fn_call(&child.constructor_fn_name(), vec![child_paddr]),
                        );

                        let mut args = Vec::new();
                        for arg in op.params.iter() {
                            if arg.ident().as_str() == "pa" {
                                args.push(child_var.clone())
                            } else {
                                let e = param_exprs[arg.ident().as_str()].clone();
                                args.push(e);
                            }
                        }

                        if_block
                            .then_branch()
                            .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);

                        body.ifelse(if_block);

                        let child_var = body.new_variable("child", child.to_ctype()).to_expr();

                        body.assign(
                            child_var.clone(),
                            C::Expr::fn_call(
                                &variant_unit.resolve_fn_name(),
                                vec![C::Expr::fn_call(
                                    &variant_unit.constructor_fn_name(),
                                    variant_unit
                                        .params_as_slice()
                                        .iter()
                                        .map(|param| C::Expr::field_access(&tunit, param.ident()))
                                        .collect(),
                                )],
                            ),
                        );
                        let mapped_sz = body
                            .new_variable("mapped_sz", C::Type::new_size())
                            .to_expr();
                        let mut args = vec![C::Expr::addr_of(&child_var)];
                        args.extend(
                            op.params
                                .iter()
                                .map(|param| param_exprs[param.ident().as_str()].clone()),
                        );

                        body.assign(
                            mapped_sz.clone(),
                            C::Expr::fn_call(&child.to_op_fn_name(op), args),
                        );
                        body.assign(
                            sz.clone(),
                            C::Expr::binop(sz.clone(), "-", mapped_sz.clone()),
                        );
                        if variant != has_children.last().unwrap() {
                            body.assign(
                                va.clone(),
                                C::Expr::binop(va.clone(), "+", mapped_sz.clone()),
                            );
                            body.assign(
                                pa.clone(),
                                C::Expr::binop(pa.clone(), "+", mapped_sz.clone()),
                            );
                        }
                    }

                    body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

                    scope.push_function(fun);
                }
                _ => {
                    let op = unit.get_method("map").unwrap();

                    let mut fun =
                        C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
                    fun.set_static().set_inline();

                    let mut param_exprs = HashMap::new();

                    let v = fun
                        .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                        .to_expr();
                    param_exprs.insert("unit", v);
                    for f in op.params.iter() {
                        let p =
                            fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
                        param_exprs.insert(f.ident().as_str(), p.to_expr());
                    }

                    let va = &param_exprs["va"];
                    let sz = &param_exprs["sz"];
                    let pa = &param_exprs["pa"];
                    let body = &mut fun.body();

                    // add assertions
                    for arg in [va, sz, pa] {
                        body.fn_call(
                            "assert",
                            vec![C::Expr::binop(
                                C::Expr::binop(
                                    arg.clone(),
                                    "%",
                                    C::Expr::new_num(base_page_size as u64),
                                ),
                                "==",
                                C::Expr::new_num(0),
                            )],
                        );
                    }

                    let original_sz = body
                        .new_variable("original_sz", C::Type::new_size())
                        .to_expr();
                    body.assign(original_sz.clone(), sz.clone());
                    let page_size: usize = 1 << dest_unit.input_bitwidth();

                    let mut if_block = C::IfElse::new(&C::Expr::binop(
                        C::Expr::binop(
                            C::Expr::binop(
                                C::Expr::binop(va.clone(), "%", C::Expr::new_num(page_size as u64)),
                                "==",
                                C::Expr::new_num(0),
                            ),
                            "&&",
                            C::Expr::binop(
                                C::Expr::binop(pa.clone(), "%", C::Expr::new_num(page_size as u64)),
                                "==",
                                C::Expr::new_num(0),
                            ),
                        ),
                        "&&",
                        C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                    ));
                    let i = if_block
                        .then_branch()
                        .new_variable("i", C::Type::new_size())
                        .to_expr();
                    if_block.then_branch().assign(
                        i.clone(),
                        C::Expr::binop(
                            va.clone(),
                            ">>",
                            C::Expr::new_num(dest_unit.input_bitwidth()),
                        ),
                    );

                    let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                        C::Expr::binop(
                            C::Expr::binop(
                                va.clone(),
                                ">>",
                                C::Expr::new_num(dest_unit.input_bitwidth()),
                            ),
                            "==",
                            i,
                        ),
                        "&&",
                        C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
                    ));

                    let op = if dest_unit.is_enum() {
                        unit.get_method("map").unwrap()
                    } else {
                        dest_unit.get_method("map").unwrap()
                    };
                    let mut args = Vec::new();
                    for arg in op.params.iter() {
                        if arg.ident().as_str() == "pa" {
                            match &arg.ptype.typeinfo {
                                velosiast::ast::VelosiAstTypeInfo::TypeRef(ty) => {
                                    let child = relations.get_unit(ty).unwrap();
                                    args.push(C::Expr::fn_call(
                                        &child.constructor_fn_name(),
                                        op.params
                                            .iter()
                                            .map(|param| {
                                                param_exprs[param.ident().as_str()].clone()
                                            })
                                            .collect(),
                                    ));
                                }
                                _ => {
                                    let e = param_exprs[arg.ident().as_str()].clone();
                                    args.push(e);
                                }
                            }
                        } else if arg.ident().as_str() == "sz" {
                            args.push(C::Expr::new_num(page_size as u64))
                        } else {
                            let e = param_exprs[arg.ident().as_str()].clone();
                            args.push(e);
                        }
                    }

                    while_block
                        .body()
                        .fn_call(&unit.to_op_fn_name_on_unit(op, dest_unit), args);
                    while_block.body().assign(
                        sz.clone(),
                        C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
                    );
                    while_block.body().assign(
                        va.clone(),
                        C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
                    );
                    while_block.body().assign(
                        pa.clone(),
                        C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
                    );

                    if_block.then_branch().while_loop(while_block);
                    body.ifelse(if_block);

                    body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

                    scope.push_function(fun);
                }
            }
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_higher_order_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    op_name: &str,
    _osspec: &VelosiAst,
) {
    let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            // TODO: Explicit map
        }
        VelosiAstStaticMap::ListComp(_) => {
            let op = unit.get_method(op_name).unwrap();

            let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
            fun.set_static().set_inline();

            let mut param_exprs = HashMap::new();

            let v = fun
                .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
                .to_expr();
            param_exprs.insert("unit", v.clone());
            for f in op.params.iter() {
                let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
                param_exprs.insert(f.ident().as_str(), p.to_expr());
            }

            let va = &param_exprs["va"];
            let sz = &param_exprs["sz"];
            let body = &mut fun.body();

            // add assertions
            for arg in [va, sz] {
                body.fn_call(
                    "assert",
                    vec![C::Expr::binop(
                        C::Expr::binop(arg.clone(), "%", C::Expr::new_num(base_page_size as u64)),
                        "==",
                        C::Expr::new_num(0),
                    )],
                );
            }

            let original_sz = body
                .new_variable("original_sz", C::Type::new_size())
                .to_expr();
            body.assign(original_sz.clone(), sz.clone());

            let mut while_block = C::WhileLoop::new(&C::Expr::binop(
                sz.clone(),
                ">=",
                C::Expr::new_num(base_page_size as u64),
            ));
            let changed = while_block
                .body()
                .new_variable("changed", C::Type::new_size())
                .to_expr();

            let mut args = vec![C::Expr::addr_of(&v)];
            args.extend(
                op.params
                    .iter()
                    .map(|param| param_exprs[param.ident().as_str()].clone()),
            );
            while_block.body().assign(
                changed.clone(),
                C::Expr::fn_call(&unit.to_op_fn_name_one(op), args),
            );
            while_block
                .body()
                .assign(sz.clone(), C::Expr::binop(sz.clone(), "-", changed.clone()));
            while_block
                .body()
                .assign(va.clone(), C::Expr::binop(va.clone(), "+", changed));

            body.while_loop(while_block);
            body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

            scope.push_function(fun);
        }
        VelosiAstStaticMap::None(_) => {
            // No map defined for this unit
        }
    }
}

fn add_higher_order_functions(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    add_higher_order_map(scope, unit, relations, osspec);
    add_higher_order_function(scope, unit, relations, "unmap", osspec);
    add_higher_order_function(scope, unit, relations, "protect", osspec);
}

struct OpConfig<'a> {
    unit: &'a VelosiAstUnitStaticMap,
    lc: &'a VelosiAstStaticMapListComp,
    relations: &'a Relations,
    osspec: &'a VelosiAst,
    param_exprs: HashMap<&'a str, C::Expr>,
    op: &'a VelosiAstMethod,
}

fn add_op_fn_body_listcomp<'a>(body: &'a mut C::Block, ctxt: OpConfig<'a>) {
    let env = ctxt.osspec.osspec().unwrap();

    body.return_expr(C::Expr::new_num(0));

    return;

    let children = ctxt.relations.get_children_units(ctxt.unit.ident());
    assert!(children.len() == 1);
    let child = &children[0];

    let page_size = 1 << ctxt.lc.inputsize;

    // we need to differentiate based on the type of the next unit, which can be a Segment or an Enum
    match child {
        VelosiAstUnit::Enum(_) => {
            if env.has_map_protect_unmap() {
                // we have something defined in the operating systems spec, so use this one!
                println!("TODO: Implement me!");
                return;
            } else {
                // nothing defined in the OS spec, we just change the things directly
                println!("TODO: Implement me!");
                return;
            }
        }
        // -----------------------------------------------------------------------------------------
        // Segments
        // -----------------------------------------------------------------------------------------
        VelosiAstUnit::Segment(seg) => {
            // The next unit type is a segment. There can be two instances of a segment here, one that
            // maps a Frame or one that maps a table.

            if env.has_map_protect_unmap() {
                let sz = &ctxt.param_exprs["sz"];
                let va = &ctxt.param_exprs["va"];

                // create the child variable
                let child_var = body
                    .new_variable("child", C::Type::new_struct("TODO_child_type").to_ptr())
                    .to_expr();
                body.assign(
                    child_var.clone(),
                    C::Expr::fn_call(
                        ctxt.unit.get_child_fn_name().as_str(),
                        vec![ctxt.param_exprs["$unit"].clone(), va.clone(), sz.clone()],
                    ),
                );

                let mut wloop = C::WhileLoop::new(&C::Expr::binop(
                    sz.clone(),
                    ">=",
                    C::Expr::new_num(page_size),
                ));

                let loop_body = wloop.body();

                if seg.maps_frame() {
                    // This entry maps a Frame. We need to perform the operation here on the entry
                    // that maps this table. We can do this by invoking the full function here.

                    let method = if ctxt.op.ident().as_str() == "map" {
                        env.get_map_method(VelosiAstTypeProperty::Frame)
                            .expect("map method not found?")
                    } else {
                        env.get_method(ctxt.op.ident.as_str())
                            .expect("didn't find the method")
                    };

                    let spec_body = method
                        .body
                        .as_ref()
                        .expect("map method didn't have a body?");

                    let child_cond = loop_body.new_ifelse(&C::Expr::binop(
                        child_var.clone(),
                        "!=",
                        C::Expr::null(),
                    ));

                    let op_cond = child_cond.then_branch().new_ifelse(&C::Expr::lnot(
                        ctxt.unit.expr_to_cpp(&ctxt.param_exprs, spec_body),
                    ));

                    op_cond.then_branch().return_expr(C::Expr::new_num(123));

                    loop_body
                        .assign(
                            va.clone(),
                            C::Expr::binop(va.clone(), "+", C::Expr::new_num(123)),
                        )
                        .assign(
                            sz.clone(),
                            C::Expr::binop(sz.clone(), "-", C::Expr::new_num(123)),
                        )
                        .assign(
                            child_var.clone(),
                            C::Expr::fn_call(
                                ctxt.unit.get_next_child_fn_name().as_str(),
                                vec![ctxt.param_exprs["$unit"].clone(), va.clone(), sz.clone()],
                            ),
                        );

                    body.new_comment("Entry: Segment mapping a frame (with OS Spec)");
                    body.while_loop(wloop);
                } else if seg.maps_table() {
                    // This entry maps a table. We need to make sure the entry has a valid table
                    // mapping before we can continue with the operation
                    unimplemented!("TODO: implement me!");
                    body.new_comment("Entry: Segment mapping a table. (with OS Spec)");

                    let _map = env.get_map_method(VelosiAstTypeProperty::Descriptor);
                } else {
                    unreachable!()
                }
            } else if seg.maps_frame() {
                // This entry maps a Frame. We need to perform the operation here on the entry
                // that maps this table.
                body.new_comment("Entry: Segment mapping a frame (direct access)");
            } else if seg.maps_table() {
                // This entry maps a table. We need to make sure the entry has a valid table
                // mapping before we can continue with the operation
                unimplemented!("TODO: implement me!");
                body.new_comment("Entry: Segment mapping a table.  (direct access)");
            } else {
                unreachable!()
            }
        }
        _ => unreachable!(),
    }
}

fn add_map_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("map").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration with Parameters
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let param_exprs = add_fn_params(fun, unit, op, osspec);

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();
    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            unimplemented!("Handling of explicit maps unimplemented");
        }
        VelosiAstStaticMap::ListComp(lc) => {
            let ctxt = OpConfig {
                unit,
                lc,
                relations,
                osspec,
                param_exprs,
                op,
            };
            add_op_fn_body_listcomp(body, ctxt);
        }
        VelosiAstStaticMap::None(_) => {
            unreachable!();
        }
    }
}

fn add_unmap_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("unmap").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration with Parameters
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let param_exprs = add_fn_params(fun, unit, op, osspec);

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let _env = osspec.osspec().unwrap();
    let body = fun.body();

    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            unimplemented!("Handling of explicit maps unimplemented");
        }
        VelosiAstStaticMap::ListComp(lc) => {
            let ctxt = OpConfig {
                unit,
                lc,
                relations,
                osspec,
                param_exprs,
                op,
            };
            add_op_fn_body_listcomp(body, ctxt);
        }
        VelosiAstStaticMap::None(_) => {
            unreachable!();
        }
    }
}

fn add_protect_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("protect").unwrap();

    // ---------------------------------------------------------------------------------------------
    // Function Declaration with Parameters
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let param_exprs = add_fn_params(fun, unit, op, osspec);

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let _env = osspec.osspec().unwrap();
    let body = fun.body();
    match &unit.map {
        VelosiAstStaticMap::Explicit(_) => {
            unimplemented!("Handling of explicit maps unimplemented");
        }
        VelosiAstStaticMap::ListComp(lc) => {
            let ctxt = OpConfig {
                unit,
                lc,
                relations,
                osspec,
                param_exprs,
                op,
            };
            add_op_fn_body_listcomp(body, ctxt);
        }
        VelosiAstStaticMap::None(_) => {
            unreachable!();
        }
    }
}

fn add_resolve_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let rtype = if let Some(ty) = env.get_extern_type_with_property(VelosiAstTypeProperty::Frame) {
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

    fun.body().return_expr(C::Expr::bfalse());

    // let cond = body.new_ifelse(&C::Expr::lnot(C::Expr::fn_call(
    //     &unit.valid_fn_name(),
    //     vec![unit_param.clone()],
    // )));
    // cond.then_branch().return_expr(C::Expr::bfalse());

    // if let Some(child) = child {
    //     if env.has_map_protect_unmap() {
    //         body.return_expr(C::Expr::fn_call(
    //             &child.resolve_fn_name(),
    //             vec![C::Expr::field_access(&unit_param, "child"), vaddr_param],
    //         ));
    //     } else {
    //         let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();
    //         body.assign(
    //             v_next_unit.clone(),
    //             C::Expr::fn_call(
    //                 &child.get_child_fn_name(),
    //                 vec![
    //                     unit_param.clone(),  // unit ptr
    //                     C::Expr::new_num(0), // VA: should be 0
    //                 ],
    //             ),
    //         )
    //         .return_expr(C::Expr::fn_call(
    //             &unit.resolve_fn_name(),
    //             vec![unit_param, vaddr_param, paddr_param],
    //         ));
    //     }
    // } else {
    //     // no child here, so we're directly doing the thing here!
    //     if env.has_map_protect_unmap() {
    //         body.assign(
    //             C::Expr::deref(&paddr_param),
    //             C::Expr::field_access(&unit_param, "frame"),
    //         )
    //         .return_expr(C::Expr::btrue());
    //     } else {
    //         body.assign(
    //             C::Expr::deref(&paddr_param),
    //             C::Expr::fn_call(&unit.translate_fn_name(), vec![unit_param, vaddr_param]),
    //         )
    //         .return_expr(C::Expr::btrue());
    //     }
    // }

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Allocate / Free Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_free_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
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
    unit: &VelosiAstUnitStaticMap,
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
// Get Child Function
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_set_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // get the child unit
    let children = relations.get_children_units(unit.ident());

    if env.has_map_protect_unmap() {
        let rtype = match children.as_slice() {
            [] => C::Type::new_void(),
            [child] => child.to_ctype_ptr(),
            _ => unreachable!(),
        };

        let fun = scope.new_function(unit.set_child_fn_name().as_str(), C::Type::new_void());
        fun.set_static().set_inline();
        fun.push_doc_str("Sets the child pointer of the unit");

        let _unit_param = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
        let _va_param = fun
            .new_param(
                "va",
                unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
            )
            .to_expr();
        let _child_param = fun.new_param("dst", rtype);
    } else {
        scope.new_comment("No set-child function needed as no environment spec available.");
    }
}

fn add_clear_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
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
        fun.body().fn_call(
            unit.set_child_fn_name().as_str(),
            vec![unit_param, va_param, C::Expr::null()],
        );
    }
}

fn add_get_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
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
    // let body = fun.body();
    // if env.has_map_protect_unmap() {
    //     body.return_expr(C::Expr::field_access(&v_param_unit, "child"));
    // } else {
    //     // body.fn_call(
    //     //     "assert",
    //     //     vec![C::Expr::fn_call(
    //     //         unit.valid_fn_name().as_str(),
    //     //         vec![v_param_unit.clone()],
    //     //     )],
    //     // );

    //     body.new_comment("get the address of the next table by calling translate");
    //     let v_next_base = body
    //         .new_variable(
    //             "next_base",
    //             unit.ptype_to_ctype(&VelosiAstTypeInfo::PhysAddr, false),
    //         )
    //         .to_expr();
    //     body.assign(
    //         v_next_base.clone(),
    //         C::Expr::fn_call(&unit.translate_fn_name(), vec![v_param_unit]),
    //     );

    //     body.new_comment("construct the new unit");
    //     let v_next_unit = body.new_variable("next_unit", child.to_ctype()).to_expr();
    //     body.fn_call(
    //         &child.constructor_fn_name(),
    //         vec![C::Expr::addr_of(&v_next_unit), v_next_base],
    //     );

    //     body.return_expr(v_next_unit);
    // }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Generators
////////////////////////////////////////////////////////////////////////////////////////////////////

/// generates the staticmap definitions
pub fn generate(
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
    outdir: &Path,
) -> Result<(), VelosiCodeGenError> {
    log::info!("Generating staticmap unit {}", unit.ident());

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

    // add systems include
    s.new_include("stddef.h", true);
    s.new_include("assert.h", true);
    s.new_include("string.h", true);

    s.new_include("types.h", false);
    s.new_include("consts.h", false);

    // adding the OS spec header here
    {
        let env = osspec.osspec().unwrap();
        s.new_include(&format!("{}.h", env.ident().to_lowercase()), true);
    }

    // adding includes for each of the children
    {
        let env = osspec.osspec().unwrap();
        if env.has_map_protect_unmap() {
            let group_roots = relations.get_group_roots();
            let mut children = relations.get_children(unit.ident()).to_vec();
            while let Some(child) = children.pop() {
                if group_roots.contains(&child) {
                    s.new_include(&format!("{}_unit.h", child.to_lowercase()), false);
                } else {
                    children.extend(relations.get_children(&child).iter().cloned());
                }
            }
        } else {
            for child in relations.get_children(unit.ident()) {
                s.new_include(&format!("{}_unit.h", child.to_lowercase()), false);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Unit Constants and Constructor
    ////////////////////////////////////////////////////////////////////////////////////////////////

    s.new_comment(" --------------------------- Constants / Constructor -------------------------");

    // add the definitions
    add_unit_constants(s, unit);
    generate_unit_struct(s, unit, relations, osspec);
    add_constructor_function(s, unit, osspec);

    s.new_comment(" ----------------------------- Allocate and free ----------------------------");

    add_allocate_function(s, unit, relations, osspec);
    add_free_function(s, unit, relations, osspec);

    s.new_comment(" ----------------------------- Address Translation  --------------------------");

    // add_set_child_fn(s, unit, relations, osspec);
    // add_clear_child_fn(s, unit, relations, osspec);
    // add_get_child_fn(s, unit, relations, osspec);

    s.new_comment(" ---------------------------- Map / Protect/ Unmap ---------------------------");

    // add_do_map_function(s, unit, relations, osspec);
    // add_do_unmap_function(s, unit, relations, osspec);
    // add_do_protect_function(s, unit, relations, osspec);

    // add_translate_function(s, unit);

    s.new_comment(" --------------------------- Higher Order Functions --------------------------");

    add_map_function(s, unit, relations, osspec);
    add_protect_function(s, unit, relations, osspec);
    add_unmap_function(s, unit, relations, osspec);

    // resolve function
    add_resolve_function(s, unit, relations, osspec);

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Saving the file
    ////////////////////////////////////////////////////////////////////////////////////////////////

    // save the scope
    log::debug!("saving the scope!");
    let filename = format!("{}_unit.h", unit.ident().to_ascii_lowercase());
    scope.set_filename(&filename);
    scope.to_file(outdir, true)?;
    Ok(())
}
