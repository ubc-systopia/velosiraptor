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
    VelosiAst, VelosiAstMethod, VelosiAstMethodProperty, VelosiAstStaticMapListComp,
    VelosiAstTypeInfo, VelosiAstTypeProperty, VelosiAstUnit, VelosiAstUnitEnum,
    VelosiAstUnitOSSpec, VelosiAstUnitSegment, VelosiAstUnitStaticMap,
};
use velosicomposition::Relations;

use super::utils::UnitUtils;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helpers
////////////////////////////////////////////////////////////////////////////////////////////////////

fn calculate_next_va(va: &C::Expr, bits: u64) -> C::Expr {
    let mask = if bits == 64 {
        0xffff_ffff_ffff_ffff
    } else {
        (1 << bits) - 1
    };
    C::Expr::binop(va.clone(), "&", C::Expr::new_num(mask))
}

fn add_fn_params<'a>(
    fun: &mut C::Function,
    unit: &VelosiAstUnitStaticMap,
    op: &'a VelosiAstMethod,
    osspec: &VelosiAst,
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
        let p = if f.ident().as_str() == "pa" {
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

// fn base_inbitwidth(relations: &Relations, ident: &Rc<String>, inbitwidth: u64) -> u64 {
//     let children = relations.get_children_units(ident);
//     if children.is_empty() {
//         inbitwidth
//     } else {
//         children
//             .iter()
//             .map(|u| base_inbitwidth(relations, u.ident(), u.input_bitwidth()))
//             .chain(std::iter::once(inbitwidth))
//             .min()
//             .unwrap()
//     }
// }

fn next_unit_type(
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) -> C::Type {
    let env = osspec.osspec().unwrap();

    let _root_units = relations.get_roots();

    match relations.get_only_child_unit(unit.ident()) {
        VelosiAstUnit::Enum(e) => {
            if env.has_map_protect_unmap() {
                C::Type::new_typedef(&unit.to_child_type_name())
            } else {
                e.as_ref().to_ctype()
            }
        }
        VelosiAstUnit::Segment(e) => {
            if env.has_map_protect_unmap() {
                C::Type::new_typedef(&unit.to_child_type_name())
            } else {
                e.as_ref().to_ctype()
            }
        }
        _ => unreachable!(),
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Unit Struct Definitions
////////////////////////////////////////////////////////////////////////////////////////////////////

fn generate_child_struct_fields_segment(
    cstruct: &mut C::Struct,
    s: &VelosiAstUnitSegment,
    env: &VelosiAstUnitOSSpec,
) {
    if s.maps_table() {
        cstruct.push_doc_str("segment mapping a descriptor");
        if let Some(frametype) =
            env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor)
        {
            cstruct.new_field("table", C::Type::new_typedef(frametype.ident.as_str()));
        } else {
            cstruct.new_field("dummy", C::Type::new_int32());
        }
    } else if s.maps_frame() {
        cstruct.push_doc_str("segment mapping a frame");
        // this one just maps a frame
        if let Some(frametype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
            cstruct.new_field("frame", C::Type::new_typedef(frametype.ident.as_str()));
        } else {
            cstruct.new_field("dummy", C::Type::new_int32());
        }
    } else {
        unreachable!()
    }
}

fn generate_child_struct_fields_enum(
    scope: &mut C::Scope,
    cstruct: &mut C::Struct,
    unit: &VelosiAstUnitStaticMap,
    e: &VelosiAstUnitEnum,
    relations: &Relations,
    env: &VelosiAstUnitOSSpec,
) {
    // create a union and an enum for all chlidren units here
    let mut children_union = C::Union::new(&unit.to_child_union_name());
    let mut children_enum = C::Enum::new(&unit.to_child_kind_name());

    let frame_type =
        if let Some(frametype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Frame) {
            C::Type::new_typedef(frametype.ident.as_str())
        } else {
            unreachable!();
        };

    // get all the children units of this enum
    let children = relations.get_children_units(e.ident());
    for child in &children {
        if let VelosiAstUnit::Segment(s) = child {
            if s.maps_frame() {
                // here we map a frame, we create a wrapper struct for the Frame type
                let mut child_struct = C::Struct::new(&child.to_struct_name());
                child_struct.new_field("frame", frame_type.clone());

                // add the child struct to the scope and add a typedef
                let child_ty = child_struct.to_type();
                scope.push_struct(child_struct);
                scope.new_typedef(&child.to_type_name(), child_ty);

                // add the entry in the child union
                children_union.new_field(
                    &child.ident().to_ascii_lowercase(),
                    C::Type::new_typedef(&child.to_type_name()),
                );
            } else if s.maps_table() {
                // if the next one is a table, then that should already have been defined
                let next = relations.get_only_child_unit(s.ident());
                children_union.new_field(&child.ident().to_ascii_lowercase(), next.to_ctype());
            } else {
                unreachable!()
            }
        } else {
            unreachable!("should always be a segment here");
        }

        children_enum.new_variant(&child.ident().to_ascii_uppercase());
    }

    // add the
    let children_enum_ty = children_enum.to_type();
    let children_union_ty = children_union.to_type();
    scope.push_enum(children_enum);
    scope.push_union(children_union);

    // add the kind and variants field to the children struct
    cstruct.new_field("kind", children_enum_ty);
    cstruct.new_field("variants", children_union_ty);
}

fn generate_child_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    env: &VelosiAstUnitOSSpec,
) {
    let mut children_struct = C::Struct::new(&unit.to_child_struct_name());
    let children_struct_ty = children_struct.to_type();

    // add the specific types for the children depending on whether they are
    match relations.get_only_child_unit(unit.ident()) {
        VelosiAstUnit::Enum(e) => {
            generate_child_struct_fields_enum(scope, &mut children_struct, unit, e, relations, env);
        }
        VelosiAstUnit::Segment(s) => {
            generate_child_struct_fields_segment(&mut children_struct, s, env);
        }
        _ => unreachable!(),
    }

    // add the book keeping information, depending on the data structure representation
    if map.is_repr_list() {
        children_struct.push_doc_str("list element");
        children_struct.new_field("next", C::Type::new_typedef_ptr(&unit.to_child_type_name()));
        children_struct.new_field(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        );
    } else if map.is_repr_array() {
        children_struct.push_doc_str("array element");
    } else {
        unreachable!();
    }

    // finally add the struct to the scope
    scope
        .push_struct(children_struct)
        .new_typedef(&unit.to_child_type_name(), children_struct_ty);
}

fn generate_unit_struct(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    let mut s = C::Struct::new(&unit.to_struct_name());
    s.push_doc_str(&format!("Unit Type `{}`", unit.ident()));
    s.push_doc_str("");
    s.push_doc_str(&format!("@loc: {}", unit.loc.loc()));

    let stype = s.to_type();

    if env.has_map_protect_unmap() {
        // -----------------------------------------------------------------------------------------
        // OSSpec defines the map/protect/unmap functions
        // -----------------------------------------------------------------------------------------

        // generate the data structure to represent the children of this unit
        generate_child_struct(scope, unit, map, relations, env);

        // Add a field for the VNode type as this is a translation table
        if let Some(etype) = env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor) {
            let f = C::Field::with_string(
                String::from("vnode"),
                unit.ptype_to_ctype(&etype.as_ref().into(), false),
            );
            s.push_field(f);
        } else {
            unimplemented!("expected a descriptor type!");
        }

        // Add the management data structure fields (list,array representation)
        let child_type = next_unit_type(unit, relations, osspec);
        let children_name = "children".to_string();
        if map.is_repr_list() {
            let f = C::Field::with_string(children_name, child_type.to_ptr());
            s.push_field(f);
        } else if map.is_repr_array() {
            // array representation
            let f =
                C::Field::with_string(children_name, child_type.to_ptr().to_array(unit.map_size()));
            s.push_field(f);
        } else {
            unreachable!()
        }
    } else {
        // -----------------------------------------------------------------------------------------
        // No OSSpec for map/unmap/protect, so we add all the unit parameters as fields
        // -----------------------------------------------------------------------------------------
        for p in &unit.params {
            let f = C::Field::with_string(p.ident().to_string(), C::Type::new_uintptr());
            s.push_field(f);
        }
    };

    // add the struct to the scope and adding a typedef
    scope.push_struct(s);
    scope.new_typedef(&unit.to_type_name(), stype);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Constructors
////////////////////////////////////////////////////////////////////////////////////////////////////

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
                let ty = unit.ptype_to_ctype(&etype.as_ref().into(), true);
                let param = fun.new_param("vnode", ty).to_expr();
                params.push(("vnode", param));

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
                (p.ident().as_str(), param)
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
                C::Expr::field_access(&unit_expr, "children"),
                C::Expr::new_num(0),
                C::Expr::size_of(&C::Expr::field_access(&unit_expr, "children")),
            ],
        );
    }

    fun.push_doc_str("constructor of the unit type");

    scope.push_function(fun);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Map/Unmap/Protect Functions
////////////////////////////////////////////////////////////////////////////////////////////////////

// fn add_do_op_fn_body_listcomp(
//     scope: &mut C::Block,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitStaticMap,
//     map: &VelosiAstStaticMapListComp,
//     op: &VelosiAstMethod,
//     variant_unit: Option<&VelosiAstUnit>,
//     mut params_exprs: HashMap<&str, C::Expr>,
// ) {
//     scope.new_comment(map.to_string().as_str());

//     let idx_var = scope.new_variable("idx", C::Type::new_size()).to_expr();

//     let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
//     let va_var = params_exprs.get("va").unwrap();

//     // idx = va / element_size
//     scope.assign(
//         idx_var.clone(),
//         C::Expr::binop(
//             va_var.clone(),
//             ">>",
//             C::Expr::ConstNum(dest_unit.input_bitwidth()),
//         ),
//     );

//     // va = va & (element_size - 1)
//     scope.assign(
//         va_var.clone(),
//         C::Expr::binop(
//             va_var.clone(),
//             "&",
//             C::Expr::binop(
//                 C::Expr::binop(
//                     C::Expr::ConstNum(1),
//                     "<<",
//                     C::Expr::ConstNum(dest_unit.input_bitwidth()),
//                 ),
//                 "-",
//                 C::Expr::ConstNum(1),
//             ),
//         ),
//     );

//     // nee d

//     let tunit = scope
//         .new_variable("targetunit", dest_unit.to_ctype())
//         .to_expr();

//     let unit_var = params_exprs.get("unit").unwrap();
//     let mut var_mappings = HashMap::new();
//     for p in unit.params_as_slice() {
//         var_mappings.insert(
//             p.ident().as_str(),
//             C::Expr::field_access(unit_var, p.ident().as_str()),
//         );
//     }

//     var_mappings.insert(map.var.ident().as_str(), idx_var);

//     // TODO here!
//     let args = map
//         .elm
//         .dst
//         .args
//         .iter()
//         .map(|p| unit.expr_to_cpp(&var_mappings, p))
//         .collect();

//     scope.assign(
//         tunit.clone(),
//         C::Expr::fn_call(&dest_unit.constructor_fn_name(), args),
//     );

//     let mut args = vec![C::Expr::addr_of(&tunit)];
//     for arg in op.params.iter() {
//         let e = params_exprs.remove(arg.ident().as_str()).unwrap();
//         args.push(e);
//     }
//     let fn_name = match variant_unit {
//         Some(variant_unit) => dest_unit.to_op_fn_name_on_unit(op, variant_unit),
//         None => dest_unit.to_op_fn_name(op),
//     };

//     scope.return_expr(C::Expr::fn_call(&fn_name, args));
// }

// fn add_op_fnunction(
//     scope: &mut C::Scope,
//     ast: &VelosiAst,
//     unit: &VelosiAstUnitStaticMap,
//     op_name: &str,
// ) {
//     match &unit.map {
//         VelosiAstStaticMap::Explicit(_) => {
//             // TODO: explicit map
//         }
//         VelosiAstStaticMap::ListComp(map) => {
//             let dest_unit = ast.get_unit(map.elm.dst.ident().as_str()).unwrap();
//             match dest_unit {
//                 VelosiAstUnit::Enum(e) if op_name == "map" => {
//                     for variant in e.get_next_unit_idents() {
//                         let variant_unit = ast.get_unit(variant).unwrap();
//                         let op = variant_unit.get_method(op_name).unwrap();

//                         // declare the function
//                         let mut fun = C::Function::with_string(
//                             unit.to_op_fn_name_on_unit(op, variant_unit),
//                             C::Type::new_size(),
//                         );
//                         fun.set_static().set_inline();

//                         let mut param_exprs = HashMap::new();

//                         let v = fun
//                             .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//                             .to_expr();
//                         param_exprs.insert("unit", v);
//                         for f in op.params.iter() {
//                             let p = fun
//                                 .new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
//                             param_exprs.insert(f.ident().as_str(), p.to_expr());
//                         }

//                         // todo: add requires

//                         add_do_op_fn_body_listcomp(
//                             fun.body(),
//                             ast,
//                             unit,
//                             map,
//                             op,
//                             Some(variant_unit),
//                             param_exprs,
//                         );

//                         // push the function to the scope
//                         scope.push_function(fun);
//                     }
//                 }
//                 _ => {
//                     let op = if dest_unit.is_enum() {
//                         unit.get_method(op_name).unwrap()
//                     } else {
//                         dest_unit.get_method(op_name).unwrap()
//                     };
//                     let fn_name = if op_name == "map" {
//                         unit.to_op_fn_name_on_unit(op, dest_unit)
//                     } else {
//                         unit.to_op_fn_name_one(op)
//                     };

//                     // declare the function
//                     let mut fun = C::Function::with_string(fn_name, C::Type::new_size());
//                     fun.set_static().set_inline();

//                     let mut param_exprs = HashMap::new();

//                     let v = fun
//                         .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//                         .to_expr();
//                     param_exprs.insert("unit", v);
//                     for f in op.params.iter() {
//                         let p =
//                             fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
//                         param_exprs.insert(f.ident().as_str(), p.to_expr());
//                     }

//                     // todo: add requires

//                     add_do_op_fn_body_listcomp(fun.body(), ast, unit, map, op, None, param_exprs);

//                     // push the function to the scope
//                     scope.push_function(fun);
//                 }
//             }
//         }
//         VelosiAstStaticMap::None(_) => {
//             // no map defined
//         }
//     }
// }

// fn add_do_map_function(
//     _scope: &mut C::Scope,
//     _unit: &VelosiAstUnitStaticMap,
//     _relations: &Relations,
//     _osspec: &VelosiAst,
// ) {
//     // let m_fn = unit.get_method("map").unwrap();
//     // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
// }

// fn add_do_unmap_function(
//     _scope: &mut C::Scope,
//     _unit: &VelosiAstUnitStaticMap,
//     _relations: &Relations,
//     _osspec: &VelosiAst,
// ) {
//     // let m_fn = unit.get_method("unmap").unwrap();
//     // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
// }

// fn add_do_protect_function(
//     _scope: &mut C::Scope,
//     _unit: &VelosiAstUnitStaticMap,
//     _relations: &Relations,
//     _osspec: &VelosiAst,
// ) {
//     // let m_fn = unit.get_method("protect").unwrap();
//     // add_op_fn(scope, unit, &childunit, m_fn, relations, osspec);
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Higher-Order Functions with Loops
////////////////////////////////////////////////////////////////////////////////////////////////////

// fn add_higher_order_map(
//     scope: &mut C::Scope,
//     unit: &VelosiAstUnitStaticMap,
//     relations: &Relations,
//     _osspec: &VelosiAst,
// ) {
//     let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(_) => {
//             // TODO: Explicit map
//         }
//         VelosiAstStaticMap::ListComp(map) => {
//             let dest_unit = &relations.get_children_units(unit.ident())[0];
//             match dest_unit {
//                 VelosiAstUnit::Enum(e) => {
//                     let op = unit.get_method("map").unwrap();

//                     let mut fun =
//                         C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
//                     fun.set_static().set_inline();

//                     let mut param_exprs = HashMap::new();

//                     let v = fun
//                         .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//                         .to_expr();
//                     param_exprs.insert("unit", v.clone());
//                     for f in op.params.iter() {
//                         let p =
//                             fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
//                         param_exprs.insert(f.ident().as_str(), p.to_expr());
//                     }

//                     let va = &param_exprs["va"];
//                     let sz = &param_exprs["sz"];
//                     let pa = &param_exprs["pa"];
//                     let body = &mut fun.body();

//                     // add assertions
//                     for arg in [va, sz, pa] {
//                         body.fn_call(
//                             "assert",
//                             vec![C::Expr::binop(
//                                 C::Expr::binop(
//                                     arg.clone(),
//                                     "%",
//                                     C::Expr::new_num(base_page_size as u64),
//                                 ),
//                                 "==",
//                                 C::Expr::new_num(0),
//                             )],
//                         );
//                     }

//                     let original_sz = body
//                         .new_variable("original_sz", C::Type::new_size())
//                         .to_expr();
//                     body.assign(original_sz.clone(), sz.clone());

//                     let (has_children, no_children): (Vec<_>, Vec<_>) = e
//                         .get_next_unit_idents()
//                         .into_iter()
//                         .partition(|variant| !relations.get_children(variant).is_empty());

//                     for variant in no_children {
//                         let variant_unit = relations.get_unit(variant).unwrap();
//                         let page_size: usize = 1 << variant_unit.input_bitwidth();

//                         let mut if_block = C::IfElse::new(&C::Expr::binop(
//                             C::Expr::binop(
//                                 C::Expr::binop(
//                                     C::Expr::binop(
//                                         va.clone(),
//                                         "%",
//                                         C::Expr::new_num(page_size as u64),
//                                     ),
//                                     "==",
//                                     C::Expr::new_num(0),
//                                 ),
//                                 "&&",
//                                 C::Expr::binop(
//                                     C::Expr::binop(
//                                         pa.clone(),
//                                         "%",
//                                         C::Expr::new_num(page_size as u64),
//                                     ),
//                                     "==",
//                                     C::Expr::new_num(0),
//                                 ),
//                             ),
//                             "&&",
//                             C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
//                         ));
//                         let i = if_block
//                             .then_branch()
//                             .new_variable("i", C::Type::new_size())
//                             .to_expr();
//                         if_block.then_branch().assign(
//                             i.clone(),
//                             C::Expr::binop(
//                                 va.clone(),
//                                 ">>",
//                                 C::Expr::new_num(variant_unit.input_bitwidth()),
//                             ),
//                         );

//                         let mut while_block = C::WhileLoop::new(&C::Expr::binop(
//                             C::Expr::binop(
//                                 C::Expr::binop(
//                                     va.clone(),
//                                     ">>",
//                                     C::Expr::new_num(variant_unit.input_bitwidth()),
//                                 ),
//                                 "==",
//                                 i,
//                             ),
//                             "&&",
//                             C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
//                         ));

//                         let mut args = Vec::new();
//                         for arg in op.params.iter() {
//                             if arg.ident().as_str() == "sz" {
//                                 args.push(C::Expr::new_num(page_size as u64))
//                             } else {
//                                 let e = param_exprs[arg.ident().as_str()].clone();
//                                 args.push(e);
//                             }
//                         }

//                         while_block
//                             .body()
//                             .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);
//                         while_block.body().assign(
//                             sz.clone(),
//                             C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
//                         );
//                         while_block.body().assign(
//                             va.clone(),
//                             C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
//                         );
//                         while_block.body().assign(
//                             pa.clone(),
//                             C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
//                         );

//                         if_block.then_branch().while_loop(while_block);
//                         body.ifelse(if_block);
//                     }

//                     for variant in &has_children {
//                         let children = relations.get_children_units(variant);
//                         let child = &children[0];
//                         let variant_unit = relations.get_unit(variant).unwrap();

//                         let i = body.new_variable("i", C::Type::new_size()).to_expr();
//                         body.assign(
//                             i.clone(),
//                             C::Expr::binop(
//                                 va.clone(),
//                                 ">>",
//                                 C::Expr::new_num(variant_unit.input_bitwidth()),
//                             ),
//                         );

//                         let tunit = body
//                             .new_variable("targetunit", (&dest_unit).to_ctype())
//                             .to_expr();

//                         let unit_var = param_exprs.get("unit").unwrap();
//                         let mut var_mappings = HashMap::new();
//                         for p in unit.params_as_slice() {
//                             var_mappings.insert(
//                                 p.ident().as_str(),
//                                 C::Expr::field_access(unit_var, p.ident().as_str()),
//                             );
//                         }

//                         var_mappings.insert(map.var.ident().as_str(), i);

//                         let args = map
//                             .elm
//                             .dst
//                             .args
//                             .iter()
//                             .map(|p| unit.expr_to_cpp(&var_mappings, p))
//                             .collect();

//                         body.assign(
//                             tunit.clone(),
//                             C::Expr::fn_call(&(&dest_unit).constructor_fn_name(), args),
//                         );

//                         let mut if_block = C::IfElse::new(&C::Expr::uop(
//                             "!",
//                             C::Expr::fn_call(&(&dest_unit).valid_fn_name(), vec![tunit.clone()]),
//                         ));
//                         let child_paddr = if_block
//                             .then_branch()
//                             .new_variable("child_paddr", C::Type::new_typedef("paddr_t"))
//                             .to_expr();
//                         if_block.then_branch().assign(
//                             child_paddr.clone(),
//                             C::Expr::fn_call(
//                                 "virt_to_phys",
//                                 vec![C::Expr::fn_call(
//                                     "alloc",
//                                     vec![C::Expr::new_num(base_page_size as u64)],
//                                 )],
//                             ),
//                         );
//                         let child_var = if_block
//                             .then_branch()
//                             .new_variable("child", child.to_ctype())
//                             .to_expr();
//                         if_block.then_branch().assign(
//                             child_var.clone(),
//                             C::Expr::fn_call(&child.constructor_fn_name(), vec![child_paddr]),
//                         );

//                         let mut args = Vec::new();
//                         for arg in op.params.iter() {
//                             if arg.ident().as_str() == "pa" {
//                                 args.push(child_var.clone())
//                             } else {
//                                 let e = param_exprs[arg.ident().as_str()].clone();
//                                 args.push(e);
//                             }
//                         }

//                         if_block
//                             .then_branch()
//                             .fn_call(&unit.to_op_fn_name_on_unit(op, variant_unit), args);

//                         body.ifelse(if_block);

//                         let child_var = body.new_variable("child", child.to_ctype()).to_expr();

//                         body.assign(
//                             child_var.clone(),
//                             C::Expr::fn_call(
//                                 &variant_unit.resolve_fn_name(),
//                                 vec![C::Expr::fn_call(
//                                     &variant_unit.constructor_fn_name(),
//                                     variant_unit
//                                         .params_as_slice()
//                                         .iter()
//                                         .map(|param| C::Expr::field_access(&tunit, param.ident()))
//                                         .collect(),
//                                 )],
//                             ),
//                         );
//                         let mapped_sz = body
//                             .new_variable("mapped_sz", C::Type::new_size())
//                             .to_expr();
//                         let mut args = vec![C::Expr::addr_of(&child_var)];
//                         args.extend(
//                             op.params
//                                 .iter()
//                                 .map(|param| param_exprs[param.ident().as_str()].clone()),
//                         );

//                         body.assign(
//                             mapped_sz.clone(),
//                             C::Expr::fn_call(&child.to_op_fn_name(op), args),
//                         );
//                         body.assign(
//                             sz.clone(),
//                             C::Expr::binop(sz.clone(), "-", mapped_sz.clone()),
//                         );
//                         if variant != has_children.last().unwrap() {
//                             body.assign(
//                                 va.clone(),
//                                 C::Expr::binop(va.clone(), "+", mapped_sz.clone()),
//                             );
//                             body.assign(
//                                 pa.clone(),
//                                 C::Expr::binop(pa.clone(), "+", mapped_sz.clone()),
//                             );
//                         }
//                     }

//                     body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

//                     scope.push_function(fun);
//                 }
//                 _ => {
//                     let op = unit.get_method("map").unwrap();

//                     let mut fun =
//                         C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
//                     fun.set_static().set_inline();

//                     let mut param_exprs = HashMap::new();

//                     let v = fun
//                         .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//                         .to_expr();
//                     param_exprs.insert("unit", v);
//                     for f in op.params.iter() {
//                         let p =
//                             fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
//                         param_exprs.insert(f.ident().as_str(), p.to_expr());
//                     }

//                     let va = &param_exprs["va"];
//                     let sz = &param_exprs["sz"];
//                     let pa = &param_exprs["pa"];
//                     let body = &mut fun.body();

//                     // add assertions
//                     for arg in [va, sz, pa] {
//                         body.fn_call(
//                             "assert",
//                             vec![C::Expr::binop(
//                                 C::Expr::binop(
//                                     arg.clone(),
//                                     "%",
//                                     C::Expr::new_num(base_page_size as u64),
//                                 ),
//                                 "==",
//                                 C::Expr::new_num(0),
//                             )],
//                         );
//                     }

//                     let original_sz = body
//                         .new_variable("original_sz", C::Type::new_size())
//                         .to_expr();
//                     body.assign(original_sz.clone(), sz.clone());
//                     let page_size: usize = 1 << dest_unit.input_bitwidth();

//                     let mut if_block = C::IfElse::new(&C::Expr::binop(
//                         C::Expr::binop(
//                             C::Expr::binop(
//                                 C::Expr::binop(va.clone(), "%", C::Expr::new_num(page_size as u64)),
//                                 "==",
//                                 C::Expr::new_num(0),
//                             ),
//                             "&&",
//                             C::Expr::binop(
//                                 C::Expr::binop(pa.clone(), "%", C::Expr::new_num(page_size as u64)),
//                                 "==",
//                                 C::Expr::new_num(0),
//                             ),
//                         ),
//                         "&&",
//                         C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
//                     ));
//                     let i = if_block
//                         .then_branch()
//                         .new_variable("i", C::Type::new_size())
//                         .to_expr();
//                     if_block.then_branch().assign(
//                         i.clone(),
//                         C::Expr::binop(
//                             va.clone(),
//                             ">>",
//                             C::Expr::new_num(dest_unit.input_bitwidth()),
//                         ),
//                     );

//                     let mut while_block = C::WhileLoop::new(&C::Expr::binop(
//                         C::Expr::binop(
//                             C::Expr::binop(
//                                 va.clone(),
//                                 ">>",
//                                 C::Expr::new_num(dest_unit.input_bitwidth()),
//                             ),
//                             "==",
//                             i,
//                         ),
//                         "&&",
//                         C::Expr::binop(sz.clone(), ">=", C::Expr::new_num(page_size as u64)),
//                     ));

//                     let op = if dest_unit.is_enum() {
//                         unit.get_method("map").unwrap()
//                     } else {
//                         dest_unit.get_method("map").unwrap()
//                     };
//                     let mut args = Vec::new();
//                     for arg in op.params.iter() {
//                         if arg.ident().as_str() == "pa" {
//                             match &arg.ptype.typeinfo {
//                                 velosiast::ast::VelosiAstTypeInfo::TypeRef(ty) => {
//                                     let child = relations.get_unit(ty).unwrap();
//                                     args.push(C::Expr::fn_call(
//                                         &child.constructor_fn_name(),
//                                         op.params
//                                             .iter()
//                                             .map(|param| {
//                                                 param_exprs[param.ident().as_str()].clone()
//                                             })
//                                             .collect(),
//                                     ));
//                                 }
//                                 _ => {
//                                     let e = param_exprs[arg.ident().as_str()].clone();
//                                     args.push(e);
//                                 }
//                             }
//                         } else if arg.ident().as_str() == "sz" {
//                             args.push(C::Expr::new_num(page_size as u64))
//                         } else {
//                             let e = param_exprs[arg.ident().as_str()].clone();
//                             args.push(e);
//                         }
//                     }

//                     while_block
//                         .body()
//                         .fn_call(&unit.to_op_fn_name_on_unit(op, dest_unit), args);
//                     while_block.body().assign(
//                         sz.clone(),
//                         C::Expr::binop(sz.clone(), "-", C::Expr::new_num(page_size as u64)),
//                     );
//                     while_block.body().assign(
//                         va.clone(),
//                         C::Expr::binop(va.clone(), "+", C::Expr::new_num(page_size as u64)),
//                     );
//                     while_block.body().assign(
//                         pa.clone(),
//                         C::Expr::binop(pa.clone(), "+", C::Expr::new_num(page_size as u64)),
//                     );

//                     if_block.then_branch().while_loop(while_block);
//                     body.ifelse(if_block);

//                     body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

//                     scope.push_function(fun);
//                 }
//             }
//         }
//         VelosiAstStaticMap::None(_) => {
//             // No map defined for this unit
//         }
//     }
// }

// fn add_higher_order_function(
//     scope: &mut C::Scope,
//     unit: &VelosiAstUnitStaticMap,
//     relations: &Relations,
//     op_name: &str,
//     _osspec: &VelosiAst,
// ) {
//     let base_page_size: usize = 1 << base_inbitwidth(relations, unit.ident(), unit.inbitwidth);

//     match &unit.map {
//         VelosiAstStaticMap::Explicit(_) => {
//             // TODO: Explicit map
//         }
//         VelosiAstStaticMap::ListComp(_) => {
//             let op = unit.get_method(op_name).unwrap();

//             let mut fun = C::Function::with_string(unit.to_op_fn_name(op), C::Type::new_size());
//             fun.set_static().set_inline();

//             let mut param_exprs = HashMap::new();

//             let v = fun
//                 .new_param("unit", C::Type::to_ptr(&unit.to_ctype()))
//                 .to_expr();
//             param_exprs.insert("unit", v.clone());
//             for f in op.params.iter() {
//                 let p = fun.new_param(f.ident(), unit.ptype_to_ctype(&f.ptype.typeinfo, true));
//                 param_exprs.insert(f.ident().as_str(), p.to_expr());
//             }

//             let va = &param_exprs["va"];
//             let sz = &param_exprs["sz"];
//             let body = &mut fun.body();

//             // add assertions
//             for arg in [va, sz] {
//                 body.fn_call(
//                     "assert",
//                     vec![C::Expr::binop(
//                         C::Expr::binop(arg.clone(), "%", C::Expr::new_num(base_page_size as u64)),
//                         "==",
//                         C::Expr::new_num(0),
//                     )],
//                 );
//             }

//             let original_sz = body
//                 .new_variable("original_sz", C::Type::new_size())
//                 .to_expr();
//             body.assign(original_sz.clone(), sz.clone());

//             let mut while_block = C::WhileLoop::new(&C::Expr::binop(
//                 sz.clone(),
//                 ">=",
//                 C::Expr::new_num(base_page_size as u64),
//             ));
//             let changed = while_block
//                 .body()
//                 .new_variable("changed", C::Type::new_size())
//                 .to_expr();

//             let mut args = vec![C::Expr::addr_of(&v)];
//             args.extend(
//                 op.params
//                     .iter()
//                     .map(|param| param_exprs[param.ident().as_str()].clone()),
//             );
//             while_block.body().assign(
//                 changed.clone(),
//                 C::Expr::fn_call(&unit.to_op_fn_name_one(op), args),
//             );
//             while_block
//                 .body()
//                 .assign(sz.clone(), C::Expr::binop(sz.clone(), "-", changed.clone()));
//             while_block
//                 .body()
//                 .assign(va.clone(), C::Expr::binop(va.clone(), "+", changed));

//             body.while_loop(while_block);
//             body.return_expr(C::Expr::binop(original_sz, "-", sz.clone()));

//             scope.push_function(fun);
//         }
//         VelosiAstStaticMap::None(_) => {
//             // No map defined for this unit
//         }
//     }
// }

// fn add_higher_order_functions(
//     scope: &mut C::Scope,
//     unit: &VelosiAstUnitStaticMap,
//     relations: &Relations,
//     osspec: &VelosiAst,
// ) {
//     add_higher_order_map(scope, unit, relations, osspec);
//     add_higher_order_function(scope, unit, relations, "unmap", osspec);
//     add_higher_order_function(scope, unit, relations, "protect", osspec);
// }

////////////////////////////////////////////////////////////////////////////////////////////////////
// Higher-Order Functions mapping a single page
////////////////////////////////////////////////////////////////////////////////////////////////////

fn op_fn_decl<'a>(
    unit: &VelosiAstUnitStaticMap,
    op: &'a VelosiAstMethod,
    osspec: &VelosiAst,
) -> (
    C::Function,
    HashMap<&'a str, C::Expr>,
    HashMap<&'a str, VelosiAstTypeInfo>,
) {
    let mut fun = C::Function::new(unit.to_hl_op_fn_name(op).as_str(), C::Type::new_size());
    fun.set_static().set_inline();
    let (param_exprs, param_types) = add_fn_params(&mut fun, unit, op, osspec);

    (fun, param_exprs, param_types)
}

fn add_op_function_segment(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    next_unit: &VelosiAstUnitSegment,
    op: &VelosiAstMethod,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // -----------------------------------------------------------------------------------------
    // Function Declaration
    // -----------------------------------------------------------------------------------------
    let (mut fun, param_exprs, _param_types) = op_fn_decl(unit, op, osspec);

    // -----------------------------------------------------------------------------------------
    // Function Body
    // -----------------------------------------------------------------------------------------

    let v_child = {
        let body = fun.body();
        body.new_comment("get the current unit");
        let child_type = next_unit_type(unit, relations, osspec).to_ptr();
        let v_child = body.new_variable("child", child_type).to_expr();
        body.assign(
            v_child.clone(),
            C::Expr::fn_call(
                &unit.get_child_fn_name(),
                vec![param_exprs["$unit"].clone(), param_exprs["va"].clone()],
            ),
        );
        v_child
    };

    let page_size = if next_unit.inbitwidth < 64 {
        1 << next_unit.inbitwidth
    } else {
        0xffff_ffff_ffff_ffff
    };

    let child_type = C::Type::new_typedef(&unit.to_child_type_name()).to_ptr();

    if next_unit.maps_frame() {
        // -----------------------------------------------------------------------------------------
        // Function Body: Segment maps to a frame (terminal)
        // -----------------------------------------------------------------------------------------
        fun.push_doc_str("Entry: Segment mapping a frame (with OSSpec)");

        // branch out on the operation. This defines what we do with the mapping_check above
        let (env_fn, mapping) = match op.ident().as_str() {
            "map" => {
                let mcheck =
                    fun.body()
                        .new_ifelse(&C::Expr::binop(v_child.clone(), "!=", C::Expr::null()));
                mcheck
                    .then_branch()
                    .new_comment("already a mapping here! this is an error, return 0")
                    .return_expr(C::Expr::new_num(0));

                // allocate the child struct
                let var = fun
                    .body()
                    .new_variable("mapping", child_type.clone())
                    .to_expr();

                let os_alloc_fns = env.get_virt_alloc_fn();
                let os_alloc_fn = os_alloc_fns.first().unwrap();
                let args = os_alloc_fn
                    .params
                    .iter()
                    .map(|p| {
                        if p.ptype.is_size() {
                            var.deref().size_of()
                        } else {
                            C::Expr::Raw(String::from("HUUUU"))
                        }
                    })
                    .collect();

                fun.body()
                    .assign(
                        var.clone(),
                        C::Expr::fn_call(os_alloc_fn.ident().as_str(), args).cast_to(child_type),
                    )
                    .new_ifelse(&C::Expr::binop(var.clone(), "==", C::Expr::null()))
                    .then_branch()
                    .return_expr(C::Expr::new_num(0));

                (
                    env.get_map_method(VelosiAstTypeProperty::Frame)
                        .expect("function not found"),
                    var,
                )
            }
            "unmap" => {
                let mcheck =
                    fun.body()
                        .new_ifelse(&C::Expr::binop(v_child.clone(), "==", C::Expr::null()));
                mcheck
                    .then_branch()
                    .new_comment("no mapping here. just return with the size to be unmapped!")
                    .return_expr(C::Expr::new_num(page_size));

                (
                    env.get_method(op.ident().as_str())
                        .expect("function not found"),
                    C::Expr::null(),
                )
            }
            "protect" => {
                let mcheck =
                    fun.body()
                        .new_ifelse(&C::Expr::binop(v_child.clone(), "==", C::Expr::null()));
                mcheck
                    .then_branch()
                    .new_comment("no mapping here. this is an error, return 0")
                    .return_expr(C::Expr::new_num(0));

                (
                    env.get_method(op.ident().as_str())
                        .expect("function not found"),
                    C::Expr::null(),
                )
            }
            _ => unreachable!(),
        };

        let var_mappings = HashMap::new();
        let env_fn_body = env_fn.body.as_ref().expect("env fn doesn't have a body");
        let map_cond = fun
            .body()
            .new_ifelse(&unit.expr_to_cpp(&var_mappings, env_fn_body));

        match op.ident().as_str() {
            "map" => {
                let block = map_cond.then_branch();
                block.new_comment("mapping successful: add to bookkeeping");
                block.assign(mapping.field_access("frame"), param_exprs["pa"].clone());
                block.fn_call(
                    &unit.set_child_fn_name(),
                    vec![
                        param_exprs["$unit"].clone(),
                        param_exprs["va"].clone(),
                        mapping.clone(),
                    ],
                );

                let block = map_cond.other_branch();
                block.new_comment("mapping failed: clean up bookkeeping");

                let os_free_fns = env.get_virt_mem_free_fn();
                let os_free_fn = os_free_fns.first().unwrap();

                let args = os_free_fn
                    .params
                    .iter()
                    .map(|p| {
                        if p.ptype.is_size() {
                            mapping.deref().size_of()
                        } else if p.ptype.is_vaddr() {
                            mapping.cast_to(C::Type::new_uintptr())
                        } else {
                            C::Expr::Raw(String::from("HUUUU"))
                        }
                    })
                    .collect();

                block.fn_call(os_free_fn.ident().as_str(), args);
            }
            "unmap" => {
                let block = map_cond.then_branch();
                block.new_comment("unmapping successful: remove from bookkeeping");
                block.fn_call(
                    &unit.clear_child_fn_name(),
                    vec![param_exprs["$unit"].clone(), param_exprs["va"].clone()],
                );
                block.new_comment("free bookkeeping structure");
                block.fn_call("os_free_fn", vec![v_child]);
            }
            "protect" => {
                /* no-op */
                let block = map_cond.then_branch();
                block.new_comment("protect successful: do-nothing. return success.");
            }
            _ => unreachable!(),
        }

        // adding success and errore returns
        map_cond
            .then_branch()
            .return_expr(C::Expr::new_num(page_size));
        map_cond.other_branch().return_expr(C::Expr::new_num(0));
    } else if next_unit.maps_table() {
        // allocate a table
        fun.push_doc_str("Entry: Segment mapping a descriptor (with OSSpec)");
        // recurse
        let body = fun.body();

        let next = relations.get_only_child_unit(next_unit.ident());
        body.return_expr(C::Expr::fn_call(&next.to_hl_op_fn_name(op), vec![]));
        unimplemented!("TODO: handle the static map with mapping table");
    } else {
        unreachable!();
    }

    scope.push_function(fun);
}

fn add_op_function_enum(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    next_unit: &VelosiAstUnitEnum,
    op: &VelosiAstMethod,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();

    // obtain the variants
    let mut variants: Vec<_> = relations
        .get_children_units(next_unit.ident())
        .into_iter()
        .map(|unit| {
            if let VelosiAstUnit::Segment(seg) = unit {
                seg
            } else {
                unreachable!(); // all should be variants
            }
        })
        .collect();
    variants.sort_by(|a, b| {
        if a.maps_frame() && b.maps_table() {
            std::cmp::Ordering::Less
        } else if a.maps_table() && b.maps_frame() {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    });

    let _child_type = C::Type::new_typedef(&unit.to_child_type_name()).to_ptr();
    let page_size = if next_unit.inbitwidth < 64 {
        1 << next_unit.inbitwidth
    } else {
        0xffff_ffff_ffff_ffff
    };

    // -----------------------------------------------------------------------------------------
    // Function Declaration
    // -----------------------------------------------------------------------------------------

    let (mut fun, param_exprs, param_types) = op_fn_decl(unit, op, osspec);

    // -----------------------------------------------------------------------------------------
    // Function Body: Check if there's already a mapping
    // -----------------------------------------------------------------------------------------

    let child_type = next_unit_type(unit, relations, osspec).to_ptr();
    let v_child = {
        let body = fun.body();
        body.new_comment("get the current unit");
        let v_child = body.new_variable("child", child_type.clone()).to_expr();
        body.assign(
            v_child.clone(),
            C::Expr::fn_call(
                &unit.get_child_fn_name(),
                vec![param_exprs["$unit"].clone(), param_exprs["va"].clone()],
            ),
        );
        v_child
    };

    let mut mcheck = C::IfElse::new(&C::Expr::binop(v_child.clone(), "==", C::Expr::null()));

    // -----------------------------------------------------------------------------------------
    // Function Body: Variant Handling
    // -----------------------------------------------------------------------------------------

    match op.ident().as_str() {
        "map" => {
            let block = mcheck.then_branch();

            let mut tmp_pexpr;
            let pexpr = if !param_types["pa"].is_paddr() {
                let methods = env.get_method_with_signature(
                    &[param_types["pa"].clone()],
                    &VelosiAstTypeInfo::PhysAddr,
                );
                if methods.is_empty() {
                    &param_exprs
                } else {
                    tmp_pexpr = param_exprs.clone();
                    let m = methods.first().unwrap();
                    tmp_pexpr.insert(
                        "pa",
                        C::Expr::fn_call(m.ident(), vec![param_exprs["pa"].clone()]),
                    );
                    &tmp_pexpr
                }
            } else {
                &param_exprs
            };

            // check whether we can do a mapping here
            let var = block.new_variable("mapping", child_type.clone()).to_expr();

            let os_alloc_fns = env.get_virt_alloc_fn();
            let os_alloc_fn = os_alloc_fns.first().unwrap();
            let args = os_alloc_fn
                .params
                .iter()
                .map(|p| {
                    if p.ptype.is_size() {
                        var.deref().size_of()
                    } else {
                        C::Expr::Raw(String::from("HUUUU"))
                    }
                })
                .collect();

            block
                .assign(
                    var.clone(),
                    C::Expr::fn_call(os_alloc_fn.ident().as_str(), args)
                        .cast_to(child_type.clone()),
                )
                .new_ifelse(&C::Expr::binop(var.clone(), "==", C::Expr::null()))
                .then_branch()
                .new_comment("couldn't allocate any memory, cannot map!")
                .return_expr(C::Expr::new_num(0));

            let os_free_fns = env.get_virt_mem_free_fn();
            let os_free_fn = os_free_fns.first().unwrap();

            for variant in &variants {
                if variant.maps_frame() {
                    // check if the frame satisfies the mapping constraints.
                    let map_op = variant.get_method("map").unwrap();
                    let cond = if !map_op.requires.is_empty() {
                        let cond = unit.expr_to_cpp(pexpr, map_op.requires.first().unwrap());
                        map_op.requires.iter().skip(1).fold(cond, |acc, r| {
                            C::Expr::binop(acc, "&&", unit.expr_to_cpp(pexpr, r))
                        })
                    } else {
                        let va_is_zero =
                            C::Expr::binop(param_exprs["va"].clone(), "==", C::Expr::new_num(0));
                        let sz_match = C::Expr::binop(
                            param_exprs["sz"].clone(),
                            "==",
                            C::Expr::new_num(page_size),
                        );
                        C::Expr::binop(va_is_zero, "&&", sz_match)
                    };
                    // if we can map it here!
                    let map_block = block.new_ifelse(&cond).then_branch();

                    let env_fn = env
                        .get_map_method(VelosiAstTypeProperty::Frame)
                        .expect("function not found");
                    let var_mappings = HashMap::new();
                    let env_fn_body = env_fn.body.as_ref().expect("env fn doesn't have a body");
                    let map_cond =
                        map_block.new_ifelse(&unit.expr_to_cpp(&var_mappings, env_fn_body));
                    let block = map_cond.then_branch();
                    block
                        .new_comment("mapping successful: add to bookkeeping")
                        .assign(
                            var.field_access("kind"),
                            C::Expr::Raw(variant.ident().to_ascii_uppercase()),
                        )
                        .assign(
                            var.field_access("variants")
                                .field_access(&variant.ident().to_ascii_lowercase())
                                .field_access("frame"),
                            param_exprs["pa"].clone(),
                        )
                        .fn_call(
                            &unit.set_child_fn_name(),
                            vec![
                                param_exprs["$unit"].clone(),
                                param_exprs["va"].clone(),
                                var.clone(),
                            ],
                        )
                        .return_expr(C::Expr::new_num(page_size));

                    let args = os_free_fn
                        .params
                        .iter()
                        .map(|p| {
                            if p.ptype.is_size() {
                                var.deref().size_of()
                            } else if p.ptype.is_vaddr() {
                                var.cast_to(C::Type::new_uintptr())
                            } else {
                                C::Expr::Raw(String::from("HUUUU"))
                            }
                        })
                        .collect();

                    map_cond
                        .other_branch()
                        .fn_call(os_free_fn.ident().as_str(), args)
                        .return_expr(C::Expr::new_num(0));
                } else if variant.maps_table() {
                    let env_fn = env
                        .get_map_method(VelosiAstTypeProperty::Descriptor)
                        .expect("function not found");

                    let child = relations.get_only_child_unit(variant.ident());

                    let rtype = if let Some(ty) =
                        env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor)
                    {
                        VelosiAstTypeInfo::Extern(ty.ident.ident().clone())
                    } else {
                        VelosiAstTypeInfo::PhysAddr
                    };

                    let os_vnode_alloc_fns: Vec<_> = env
                        .get_method_with_property(&VelosiAstMethodProperty::MAlloc)
                        .into_iter()
                        .filter(|m| m.rtype.typeinfo.compatible(&rtype))
                        .collect();
                    let os_vnode_alloc = os_vnode_alloc_fns.first().unwrap();

                    block
                        .new_comment("Allocate a new table for the mapping")
                        .assign(
                            var.field_access("kind"),
                            C::Expr::Raw(variant.ident().to_ascii_uppercase()),
                        )
                        .assign(
                            var.field_access("variants")
                                .field_access(&variant.ident().to_ascii_lowercase())
                                .field_access("vnode"),
                            C::Expr::fn_call(
                                os_vnode_alloc.ident(),
                                vec![C::Expr::new_var(
                                    &child.to_type_enum_name(),
                                    C::Type::new_void(),
                                )],
                            ),
                        )
                        .new_comment("Perform the mapping");

                    let mut var_mappings = HashMap::new();
                    var_mappings.insert(
                        "pa",
                        var.field_access("variants")
                            .field_access(&variant.ident().to_ascii_lowercase())
                            .field_access("vnode"),
                    );
                    let env_fn_body = env_fn.body.as_ref().expect("env fn doesn't have a body");
                    let map_cond = block.new_ifelse(&unit.expr_to_cpp(&var_mappings, env_fn_body));

                    let block = map_cond.then_branch();

                    block
                        .new_comment("mapping successful: add to bookkeeping")
                        .fn_call(
                            &unit.set_child_fn_name(),
                            vec![
                                param_exprs["$unit"].clone(),
                                param_exprs["va"].clone(),
                                var.clone(),
                            ],
                        )
                        .assign(v_child.clone(), var.clone());

                    // mapping has failed
                    let args = os_free_fn
                        .params
                        .iter()
                        .map(|p| {
                            if p.ptype.is_size() {
                                var.deref().size_of()
                            } else if p.ptype.is_vaddr() {
                                var.cast_to(C::Type::new_uintptr())
                            } else {
                                C::Expr::Raw(String::from("HUUUU"))
                            }
                        })
                        .collect();
                    let block = map_cond.other_branch();
                    block
                        .new_comment("mapping has failed")
                        .fn_call(os_free_fn.ident().as_str(), args)
                        .return_expr(C::Expr::new_num(0));
                } else {
                    unreachable!();
                }
            }
        }
        "unmap" => {
            mcheck
                .then_branch()
                .new_comment("no mapping here. just return with the size to be unmapped!")
                .return_expr(C::Expr::new_num(page_size));
        }
        "protect" => {
            mcheck
                .then_branch()
                .new_comment("no mapping here. we can't do protection!")
                .return_expr(C::Expr::new_num(0));
        }
        _ => unreachable!(),
    }

    // now we handle the variants
    let mut swi = C::Switch::new(&v_child.field_access("kind"));
    for variant in &variants {
        // create the switch case
        let case = swi.new_case(C::Expr::new_var(
            &variant.ident().to_ascii_uppercase(),
            C::Type::new_enum(&unit.to_child_kind_name()),
        ));

        if variant.maps_table() {
            let next_unit = relations.get_only_child_unit(variant.ident());
            case.new_comment("this is a table mapping, recurse to next unit");
            // recurse
            let mut args = vec![v_child
                .field_access("variants")
                .field_access(&variant.ident().to_ascii_lowercase())
                .addr_of()];
            args.extend(
                op.params
                    .iter()
                    .map(|p| param_exprs[p.ident().as_str()].clone()),
            );

            case.return_expr(C::Expr::fn_call(&next_unit.to_hl_op_fn_name(op), args));
        } else if variant.maps_frame() {
            match op.ident().as_str() {
                "map" => {
                    // mapping of a super page was handled above already, so we just need to recurse
                    case.new_comment("there was a frame mapped already, return error");
                    case.return_expr(C::Expr::new_num(0));
                }
                "unmap" => {
                    case.new_comment("this is a frame mapping. check if size matches");
                    case.new_ifelse(&C::Expr::binop(
                        C::Expr::binop(param_exprs["va"].clone(), "!=", C::Expr::new_num(0)),
                        "||",
                        C::Expr::binop(
                            param_exprs["sz"].clone(),
                            "!=",
                            C::Expr::new_num(page_size),
                        ),
                    ))
                    .then_branch()
                    .return_expr(C::Expr::new_num(0));

                    let env_fn = env.get_method("unmap").expect("no method!");

                    // get the free function
                    let free_fns = env.get_virt_mem_free_fn();
                    let free_fn = free_fns.first().expect("there was no free function!");

                    let var_mappings = HashMap::new();
                    let env_fn_body = env_fn.body.as_ref().expect("env fn doesn't have a body");
                    let op_cond = case.new_ifelse(&unit.expr_to_cpp(&var_mappings, env_fn_body));
                    op_cond
                        .then_branch()
                        .new_comment(
                            "free up the book-keeping data structures of the frame mapping",
                        )
                        .fn_call(
                            free_fn.ident(),
                            vec![
                                v_child.clone().cast_to(C::Type::new_uintptr()),
                                C::Expr::size_of(&v_child.deref()),
                            ],
                        )
                        .return_expr(C::Expr::new_num(page_size));
                }
                "protect" => {
                    // child == 0
                    case.new_comment("this is a frame mapping. check if size matches");
                    case.new_ifelse(&C::Expr::binop(
                        C::Expr::binop(param_exprs["va"].clone(), "!=", C::Expr::new_num(0)),
                        "||",
                        C::Expr::binop(
                            param_exprs["sz"].clone(),
                            "!=",
                            C::Expr::new_num(page_size),
                        ),
                    ))
                    .then_branch()
                    .return_expr(C::Expr::new_num(0));

                    let env_fn = env.get_method("protect").expect("no method!");

                    let var_mappings = HashMap::new();
                    let env_fn_body = env_fn.body.as_ref().expect("env fn doesn't have a body");
                    let op_cond = case.new_ifelse(&unit.expr_to_cpp(&var_mappings, env_fn_body));
                    op_cond
                        .then_branch()
                        .return_expr(C::Expr::new_num(page_size));
                }
                _ => unreachable!(),
            }
        } else {
            unreachable!();
        }
    }

    // build up the function body
    fun.body()
        .ifelse(mcheck)
        .switch(swi)
        .return_expr(C::Expr::new_num(0));

    // add function to scope
    scope.push_function(fun);
}

fn add_op_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    _map: &VelosiAstStaticMapListComp,
    op: &VelosiAstMethod,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();
    if env.has_map_protect_unmap() {
        // -----------------------------------------------------------------------------------------
        // Function Body: Resolution through the function
        // -----------------------------------------------------------------------------------------
        match relations.get_only_child_unit(unit.ident()) {
            VelosiAstUnit::Enum(e) => add_op_function_enum(scope, unit, e, op, relations, osspec),
            VelosiAstUnit::Segment(s) => {
                add_op_function_segment(scope, unit, s, op, relations, osspec)
            }
            _ => unreachable!(),
        }
    } else {
        // function header decl
        let (mut fun, param_exprs, _param_types) = op_fn_decl(unit, op, osspec);

        // -----------------------------------------------------------------------------------------
        // Function Body: Direct Implementation
        // -----------------------------------------------------------------------------------------

        let body = fun.body();
        body.new_comment("Entry: Segment mapping a frame (direct access)");

        body.new_comment("Get the child unit (i.e., the map entry)");
        let child = relations.get_only_child_unit(unit.ident());
        let v_child = body.new_variable("child", child.to_ctype()).to_expr();
        body.assign(
            v_child.clone(),
            C::Expr::fn_call(
                &unit.get_child_fn_name(),
                vec![param_exprs["$unit"].clone(), param_exprs["va"].clone()],
            ),
        );

        body.new_comment("Recurse on child unit");
        let mut args = vec![C::Expr::addr_of(&v_child)];
        args.extend(op.params.iter().map(|p| {
            if p.ident().as_str() == "va" {
                calculate_next_va(&param_exprs[p.ident().as_str()], child.input_bitwidth())
            } else {
                param_exprs[p.ident().as_str()].clone()
            }
        }));
        body.return_expr(C::Expr::fn_call(&child.to_hl_op_fn_name(op), args));

        // add function to the scope
        scope.push_function(fun);
    }
}

fn add_map_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("map").unwrap();
    add_op_function(scope, unit, map, op, relations, osspec);
}

fn add_unmap_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("unmap").unwrap();
    add_op_function(scope, unit, map, op, relations, osspec);
}

fn add_protect_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let op = unit.get_method("protect").unwrap();
    add_op_function(scope, unit, map, op, relations, osspec);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Resolve Function
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_resolve_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
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

    if env.has_map_protect_unmap() {
        // -----------------------------------------------------------------------------------------
        // Function Body: Implementation for OS Spec
        // -----------------------------------------------------------------------------------------
        let body = fun.body();
        body.new_comment("resolve through OS spec");

        let child_type = next_unit_type(unit, relations, osspec).to_ptr();
        let v_child = body.new_variable("child", child_type).to_expr();
        body.assign(
            v_child.clone(),
            C::Expr::fn_call(
                &unit.get_child_fn_name(),
                vec![unit_param.clone(), vaddr_param.clone()],
            ),
        );

        body.new_ifelse(&C::Expr::binop(v_child.clone(), "==", C::Expr::null()))
            .then_branch()
            .return_expr(C::Expr::bfalse());

        match relations.get_only_child_unit(unit.ident()) {
            VelosiAstUnit::Enum(en) => {
                let switch = body.new_switch(&C::Expr::field_access(&v_child, "kind"));
                for child in relations.get_children_units(en.ident()) {
                    let b = switch.new_case(C::Expr::new_var(
                        &child.ident().to_ascii_uppercase(),
                        C::Type::new_enum(&unit.to_child_kind_name()),
                    ));
                    let variant_field = C::Expr::field_access(&v_child, "variants");
                    let child_variant =
                        C::Expr::field_access(&variant_field, &child.ident().to_ascii_lowercase());
                    if let VelosiAstUnit::Segment(seg) = &child {
                        if seg.maps_frame() {
                            b.new_comment("entry maps an enum -> segment mapping a frame");
                            // just return it

                            let frame_field = C::Expr::field_access(&child_variant, "frame");

                            b.assign(C::Expr::deref(&paddr_param), C::Expr::addr_of(&frame_field));
                            b.return_expr(C::Expr::btrue());
                        } else if seg.maps_table() {
                            b.new_comment("entry maps an enum -> segment mapping a table");

                            b.new_comment("segment maps a table, recurse to next unit");

                            let next_unit = relations.get_only_child_unit(seg.ident());

                            b.return_expr(C::Expr::fn_call(
                                &next_unit.resolve_fn_name(),
                                vec![
                                    C::Expr::addr_of(&child_variant),
                                    vaddr_param.clone(),
                                    paddr_param.clone(),
                                ],
                            ));
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }
            }
            VelosiAstUnit::Segment(seg) => {
                if seg.maps_frame() {
                    body.new_comment("segment maps a frame, return it!");

                    body.assign(
                        C::Expr::deref(&paddr_param),
                        C::Expr::addr_of(&C::Expr::field_access(&v_child, "frame")),
                    );

                    body.return_expr(C::Expr::btrue());
                } else if seg.maps_table() {
                    body.new_comment("segment maps a table, recurse to next unit");
                    body.return_expr(C::Expr::fn_call(
                        &seg.as_ref().resolve_fn_name(),
                        vec![C::Expr::addr_of(&v_child), vaddr_param, paddr_param],
                    ));
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        }
    } else {
        // -----------------------------------------------------------------------------------------
        // Function Body: Direct Implementation
        // -----------------------------------------------------------------------------------------
        let body = fun.body();
        body.new_comment("resolve directly");

        let child = relations.get_only_child_unit(unit.ident());

        body.new_comment("get the child unit");
        let v_child = body.new_variable("child", child.to_ctype()).to_expr();
        body.assign(
            v_child.clone(),
            C::Expr::fn_call(
                &unit.get_child_fn_name(),
                vec![unit_param.clone(), vaddr_param.clone()],
            ),
        );
        body.new_comment("recurse on next unit");
        body.return_expr(C::Expr::fn_call(
            &child.resolve_fn_name(),
            vec![
                C::Expr::addr_of(&v_child),
                calculate_next_va(&vaddr_param, child.input_bitwidth()),
                paddr_param,
            ],
        ));
    }

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
) -> bool {
    let env = osspec.osspec().unwrap();

    // ---------------------------------------------------------------------------------------------
    // Checking whether there is a free function.
    //  1) there is only a free function for the group roots
    //  2) only if the unit has memory state
    //  3) only if the OSSpec defines a free function
    // ---------------------------------------------------------------------------------------------

    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return false;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return false;
    }

    let unit_params_with_addr =
        unit.params
            .iter()
            .fold(0, |acc, p| if p.ptype.is_addr() { acc + 1 } else { acc });

    if unit_params_with_addr != 1 {
        scope.new_comment("Unit doesn't have an address parameter. Skipping allocator function.");
    }

    let os_free_fns = if env.has_map_protect_unmap() {
        let ptype = if let Some(ty) =
            env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor)
        {
            VelosiAstTypeInfo::Extern(ty.ident.ident().clone())
        } else {
            VelosiAstTypeInfo::VirtAddr
        };

        env.get_method_with_property(&VelosiAstMethodProperty::MFree)
            .into_iter()
            .filter(|m| m.params.len() == 1 && m.params[0].ptype.typeinfo.compatible(&ptype))
            .collect()
    } else {
        env.get_phys_mem_free_fn()
    };

    let os_free_fn = match os_free_fns.as_slice() {
        [] => {
            scope.new_comment("OSSpec doesn't define an free function.");
            return false;
        }
        [f] => f,
        _ => unreachable!("OSSpec defines multiple free functions?!?"),
    };

    // ---------------------------------------------------------------------------------------------
    // Function Signature
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(&unit.to_free_fn_name(), C::Type::new_void());
    fun.set_inline().set_static();

    // docstring
    fun.push_doc_str("frees memory that holds the in-memory state of the unit");

    // function parameters
    // the param type here depending on the
    let ptype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr()
    } else {
        unit.to_ctype()
    };
    let unit_param = fun.new_param("unit", ptype).to_expr();

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let fun_body = fun.body();

    if env.has_map_protect_unmap() {
        // OSSpec that sets the map/unmap functions here
        fun_body.new_comment("free up the vnode resources");
        fun_body.fn_call(os_free_fn.ident(), vec![unit_param.field_access("vnode")]);

        // get the free function
        let free_fns = env.get_virt_mem_free_fn();
        let free_fn = free_fns.first().expect("there was no free function!");

        fun_body.new_comment("free up the book-keeping data structures");
        fun_body.fn_call(
            free_fn.ident(),
            vec![
                unit_param.clone().cast_to(C::Type::new_uintptr()),
                C::Expr::size_of(&unit_param.deref()),
            ],
        );
    } else {
        // No OSSpec that sets the map/unmap functions here, in this case we can simply
        // free the memory pointed to by the corresponding field in the struct

        let units = relations.get_units();
        let memory_state_size = unit.in_memory_state_size(units);

        // now we loop over the unit parameters, and free up the memory pointed to by the
        // struct parameter, note this doesn't free the struct itself as it is assumed to
        // be allocated on the stack
        for up in &unit.params {
            match &up.ptype.typeinfo {
                VelosiAstTypeInfo::PhysAddr => {
                    let args = os_free_fn
                        .params
                        .iter()
                        .map(|p| match p.ptype.typeinfo {
                            VelosiAstTypeInfo::Size => {
                                /* size */
                                C::Expr::new_num(memory_state_size)
                            }
                            VelosiAstTypeInfo::PhysAddr => {
                                /* the allocated address */
                                C::Expr::field_access(&unit_param, up.ident().as_str())
                            }
                            _ => unreachable!(),
                        })
                        .collect();

                    // this is one we need to free
                    fun_body.fn_call(os_free_fn.ident().as_str(), args);
                }
                _ => unimplemented!(),
            }
        }
    }
    true
}

fn add_allocate_function(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    relations: &Relations,
    osspec: &VelosiAst,
) -> bool {
    let env = osspec.osspec().unwrap();

    // ---------------------------------------------------------------------------------------------
    // Checking whether there is a free function.
    //  1) there is only a free function for the group roots
    //  2) only if the unit has memory state
    //  3) only if the OSSpec defines a free function
    // ---------------------------------------------------------------------------------------------

    if !relations.get_group_roots().contains(unit.ident()) {
        scope.new_comment("not a group root, cannot allocate");
        return false;
    }

    if !unit.has_memory_state() {
        scope.new_comment("no memory state, cannot allocate");
        return false;
    }

    let unit_params_with_addr =
        unit.params
            .iter()
            .fold(0, |acc, p| if p.ptype.is_addr() { acc + 1 } else { acc });

    if unit_params_with_addr == 0 {
        scope.new_comment("Unit doesn't have an address parameter. Skipping allocator function.");
        return false;
    } else if unit_params_with_addr != 1 {
        scope.new_comment("OSSpec doesn't define an allocation function.");
        return false;
    }

    let os_alloc_fns = if env.has_map_protect_unmap() {
        let rtype = if let Some(ty) =
            env.get_extern_type_with_property(&VelosiAstTypeProperty::Descriptor)
        {
            VelosiAstTypeInfo::Extern(ty.ident.ident().clone())
        } else {
            VelosiAstTypeInfo::PhysAddr
        };

        env.get_method_with_property(&VelosiAstMethodProperty::MAlloc)
            .into_iter()
            .filter(|m| m.rtype.typeinfo.compatible(&rtype))
            .collect()
    } else {
        env.get_phys_alloc_fn()
    };

    let os_alloc_fn = match os_alloc_fns.as_slice() {
        [] => {
            scope.new_comment("OSSpec doesn't define an allocation function.");
            return false;
        }
        [f] => f,
        _ => unreachable!("OSSpec defines multiple allocator functions?!?"),
    };

    // ---------------------------------------------------------------------------------------------
    // Function Signature
    // ---------------------------------------------------------------------------------------------

    let fun = scope.new_function(&unit.to_allocate_fn_name(), C::Type::new_bool());
    fun.set_inline().set_static();

    // docstring
    fun.push_doc_str("allocates memory to hold the in-memory state of the unit");

    // parameter where the function returns the newly allocated unit
    let ptype = if env.has_map_protect_unmap() {
        unit.to_ctype().to_ptr().to_ptr()
    } else {
        unit.to_ctype().to_ptr()
    };
    let unit_param = fun.new_param("unit", ptype.clone()).to_expr();

    // ---------------------------------------------------------------------------------------------
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let fun_body = fun.body();
    if env.has_map_protect_unmap() {
        // OSSpec that sets the map/unmap functions here
        let malloc_fns = env.get_virt_alloc_fn();
        let malloc_fn = malloc_fns.first().expect("there was no allocate function");

        let args = malloc_fn
            .params
            .iter()
            .map(|p| match p.ptype.typeinfo {
                VelosiAstTypeInfo::Size => {
                    /* size */
                    C::Expr::size_of(&unit_param.deref().deref())
                }
                _ => unreachable!(),
            })
            .collect();

        fun_body.assign(
            unit_param.deref(),
            C::Expr::fn_call(malloc_fn.ident().as_str(), args).cast_to(ptype.to_deref().unwrap()),
        );

        fun_body
            .new_ifelse(&C::Expr::binop(
                unit_param.deref(),
                "==",
                C::Expr::new_num(0),
            ))
            .then_branch()
            .return_expr(C::Expr::bfalse());

        fun_body.new_comment("TODO: check for allocation success!");
        fun_body.assign(
            unit_param.deref().field_access("vnode"),
            C::Expr::fn_call(
                os_alloc_fn.ident(),
                vec![C::Expr::new_var(
                    &unit.to_type_enum_name(),
                    C::Type::new_void(),
                )],
            ),
        );

        fun_body.return_expr(C::Expr::btrue());
    } else {
        // No OSSpec that sets the map/unmap functions here, in this case we can
        // simply call the allocator function and set the return value in the corresponding
        // field in the struct. Note, the struct itself isnt' allocated on the stack.

        let units = relations.get_units();
        let memory_state_size = unit.in_memory_state_size(units);

        for p in &unit.params {
            match &p.ptype.typeinfo {
                VelosiAstTypeInfo::PhysAddr => {
                    let args = os_alloc_fn
                        .params
                        .iter()
                        .map(|p| match p.ptype.typeinfo {
                            VelosiAstTypeInfo::Size => {
                                /* size */
                                C::Expr::new_num(memory_state_size)
                            }
                            VelosiAstTypeInfo::PhysAddr => {
                                /* alignment */
                                // TODO: find alignment constraints from parent unit!
                                C::Expr::new_num(memory_state_size)
                            }
                            _ => unreachable!(),
                        })
                        .collect();

                    fun_body.assign(
                        C::Expr::field_access(&unit_param, p.ident().as_str()),
                        C::Expr::fn_call(os_alloc_fn.ident().as_str(), args),
                    );
                    fun_body
                        .new_ifelse(&C::Expr::binop(
                            C::Expr::field_access(&unit_param, p.ident().as_str()),
                            "==",
                            C::Expr::new_num(0),
                        ))
                        .then_branch()
                        .return_expr(C::Expr::bfalse());
                }
                _ => unimplemented!(),
            }
        }
        fun_body.return_expr(C::Expr::btrue());
    }

    true
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Get Child Function
////////////////////////////////////////////////////////////////////////////////////////////////////

fn add_set_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
) {
    let env = osspec.osspec().unwrap();
    if !env.has_map_protect_unmap() {
        scope.new_comment("No set-child function needed as no environment spec available.");
        return;
    }

    // get the child unit
    let children = relations.get_children_units(unit.ident());
    let (child, rtype) = match children.as_slice() {
        [child] => (
            child,
            C::Type::new_typedef(&unit.to_child_type_name()).to_ptr(),
        ),
        _ => unreachable!(),
    };

    // define the function
    let fun = scope.new_function(unit.set_child_fn_name().as_str(), C::Type::new_void());
    fun.set_static().set_inline();
    fun.push_doc_str("Sets the child pointer of the unit");

    // function parameters
    let v_unit_param = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
    let v_va_param = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();
    let v_child_param = fun.new_param("dst", rtype).to_expr();

    // function body
    let fun_body = fun.body();

    if map.elm.offset.is_some() {
        unimplemented!()
    }
    if map.is_repr_list() {
        // find the right child unit for the VA mapping
        unimplemented!("TODO - handling of list representation not done");
    } else if map.is_repr_array() {
        // here we have elements that are easily accessible
        let v_idx = fun_body.new_variable("idx", C::Type::new_size()).to_expr();
        fun_body.assign(
            v_idx.clone(),
            C::Expr::binop(
                v_va_param.clone(),
                ">>",
                C::Expr::new_num(child.input_bitwidth()),
            ),
        );
        fun_body.fn_call(
            "assert",
            vec![C::Expr::binop(
                C::Expr::binop(
                    C::Expr::array_access(
                        &C::Expr::field_access(&v_unit_param, "children"),
                        &v_idx,
                    ),
                    "==",
                    C::Expr::null(),
                ),
                "||",
                C::Expr::binop(v_child_param.clone(), "==", C::Expr::null()),
            )],
        );
        fun_body.assign(
            C::Expr::array_access(&C::Expr::field_access(&v_unit_param, "children"), &v_idx),
            v_child_param,
        );
    } else {
        unreachable!("Expected either array or list representation");
    }
}

fn add_clear_child_fn(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    _map: &VelosiAstStaticMapListComp,
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
    map: &VelosiAstStaticMapListComp,
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

    // obtain the return type
    let rtype = if env.has_map_protect_unmap() {
        C::Type::new_typedef(&unit.to_child_type_name()).to_ptr()
    } else {
        child.to_ctype()
    };

    //
    // Define the function
    // ---------------------------------------------------------------------------------------------
    let fun = scope.new_function(unit.get_child_fn_name().as_str(), rtype);
    fun.set_static().set_inline();
    fun.push_doc_str("Gets the child pointer of the unit");

    // function parameters
    let v_param_unit = fun.new_param("unit", unit.to_ctype_ptr()).to_expr();
    let v_param_va = fun
        .new_param(
            "va",
            unit.ptype_to_ctype(&VelosiAstTypeInfo::VirtAddr, false),
        )
        .to_expr();

    //
    // Function Body
    // ---------------------------------------------------------------------------------------------

    let body = fun.body();
    body.fn_call(
        "assert",
        vec![C::Expr::binop(
            v_param_va.clone(),
            "<",
            C::Expr::new_num(1 << unit.inbitwidth),
        )],
    );

    if env.has_map_protect_unmap() {
        body.new_comment("has OS interface, use the data structure instead!");

        if map.elm.offset.is_some() {
            unimplemented!()
        }
        if map.is_repr_list() {
            // find the right child unit for the VA mapping
            unimplemented!("TODO - handling of list representation not done");
        } else if map.is_repr_array() {
            // here we have elements that are easily accessible
            let v_idx = body.new_variable("idx", C::Type::new_size()).to_expr();
            body.assign(
                v_idx.clone(),
                C::Expr::binop(
                    v_param_va.clone(),
                    ">>",
                    C::Expr::new_num(child.input_bitwidth()),
                ),
            );
            body.return_expr(C::Expr::array_access(
                &C::Expr::field_access(&v_param_unit, "children"),
                &v_idx,
            ));
        } else {
            unreachable!("Expected either array or list representation");
        }
    } else if let Some(_x) = &map.elm.src {
        // specific source ranges not yet supported
        unimplemented!();
    } else {
        if map.elm.offset.is_some() {
            unimplemented!()
        }

        // here we have elements that are easily accessible
        let v_idx = body.new_variable("idx", C::Type::new_size()).to_expr();
        body.assign(
            v_idx.clone(),
            C::Expr::binop(
                v_param_va.clone(),
                ">>",
                C::Expr::new_num(child.input_bitwidth()),
            ),
        );

        let v_child_unit = body.new_variable("child_unit", child.to_ctype()).to_expr();

        let mut mappings = HashMap::new();
        mappings.insert(map.var.ident().as_str(), v_idx.clone());
        for param in &unit.params {
            mappings.insert(
                param.ident().as_str(),
                C::Expr::field_access(&v_param_unit, param.ident().as_str()),
            );
        }

        let mut args = vec![C::Expr::addr_of(&v_child_unit)];

        args.extend(
            map.elm
                .dst
                .args
                .iter()
                .map(|f| unit.expr_to_cpp(&mappings, f)),
        );

        body.fn_call(&child.constructor_fn_name(), args);
        body.return_expr(v_child_unit);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Generators
////////////////////////////////////////////////////////////////////////////////////////////////////

/// generates the staticmap definitions
pub fn generate(
    scope: &mut C::Scope,
    unit: &VelosiAstUnitStaticMap,
    map: &VelosiAstStaticMapListComp,
    relations: &Relations,
    osspec: &VelosiAst,
    _outdir: &Path,
) {
    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Unit Constants and Constructor
    ////////////////////////////////////////////////////////////////////////////////////////////////

    scope.new_comment(
        " -------------------------------- Constructor --------------------------------",
    );

    generate_unit_struct(scope, unit, map, relations, osspec);
    add_constructor_function(scope, unit, osspec);

    scope.new_comment(
        " ----------------------------- Allocate and free ----------------------------",
    );

    add_allocate_function(scope, unit, relations, osspec);
    add_free_function(scope, unit, relations, osspec);

    scope.new_comment(
        " ----------------------------- Accessing Children  --------------------------",
    );

    add_set_child_fn(scope, unit, map, relations, osspec);
    add_clear_child_fn(scope, unit, map, relations, osspec);
    add_get_child_fn(scope, unit, map, relations, osspec);

    scope.new_comment(
        " ---------------------------- Map / Protect/ Unmap ---------------------------",
    );

    // add_do_map_function(s, unit, relations, osspec);
    // add_do_unmap_function(s, unit, relations, osspec);
    // add_do_protect_function(s, unit, relations, osspec);

    // add_translate_function(s, unit);

    scope.new_comment(
        " --------------------------- Higher Order Functions --------------------------",
    );

    add_map_function(scope, unit, map, relations, osspec);
    add_protect_function(scope, unit, map, relations, osspec);
    add_unmap_function(scope, unit, map, relations, osspec);

    // resolve function
    add_resolve_function(scope, unit, relations, osspec);
}
