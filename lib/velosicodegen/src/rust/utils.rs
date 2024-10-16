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

//! Rust code generation utilities

// std includes

use std::fs;
use std::path::Path;
use std::rc::Rc;

// get the code generator
use codegen_rs as CG;

use velosiast::ast::{
    VelosiAstBinOp, VelosiAstExpr, VelosiAstInterface, VelosiAstParam, VelosiAstUnOp, VelosiOpExpr,
    VelosiOperation,
};
use velosiast::{VelosiAst, VelosiAstMethod};
//
use velosiast::ast::{VelosiAstConst, VelosiAstTypeInfo};

use crate::VelosiCodeGenError;
use crate::COPYRIGHT;

/// converts a string slice into a rustified string name
/// field_name  --> struct FieldName
pub fn to_struct_name(s: &str, suffix: Option<&str>) -> String {
    let mut c = s.chars();
    let mut s = match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
    .replace('_', "");

    if let Some(x) = suffix {
        s.push_str(x);
    }
    s
}

/// converts a string slice into a rusified constant identifier
pub fn to_const_name(s: &str) -> String {
    s.to_uppercase()
}

/// obtains the appropriate rust type for
pub fn num_to_rust_type(l: u64) -> &'static str {
    match l {
        0..=8 => "u8",
        9..=16 => "u16",
        17..=32 => "u32",
        33..=64 => "u64",
        65..=128 => "u128",
        _ => "unknown",
    }
}

/// obtains the appropriate rust type for the type info
pub fn vrs_type_to_rust_type(ty: &VelosiAstTypeInfo) -> String {
    match ty {
        VelosiAstTypeInfo::Integer => "u64".to_string(),
        VelosiAstTypeInfo::Bool => "bool".to_string(),
        VelosiAstTypeInfo::GenAddr => "GenAddr".to_string(),
        VelosiAstTypeInfo::VirtAddr => "VirtAddr".to_string(),
        VelosiAstTypeInfo::PhysAddr => "PhysAddr".to_string(),
        VelosiAstTypeInfo::Size => "usize".to_string(),
        VelosiAstTypeInfo::Flags => "Flags".to_string(),
        VelosiAstTypeInfo::TypeRef(s) => to_struct_name(s, None),
        VelosiAstTypeInfo::Range => todo!(),
        VelosiAstTypeInfo::State => todo!(),
        VelosiAstTypeInfo::Interface => todo!(),
        VelosiAstTypeInfo::Void => todo!(),
        VelosiAstTypeInfo::Extern(_) => todo!(),
        VelosiAstTypeInfo::SelfType => todo!(),
    }
}

/// converts a [VelosiAstExpr] into a string representing the corresponding rust expression
pub fn astexpr_to_rust_expr(expr: &VelosiAstExpr, ident_ctx: Option<&VelosiAst>) -> String {
    match expr {
        VelosiAstExpr::IdentLiteral(i) => {
            if let Some(ast) = ident_ctx {
                if let VelosiAstTypeInfo::TypeRef(ty) = &i.etype {
                    println!("tye: {ty:?}");
                    println!("params: {:?}", ast.get_unit(ty).unwrap().params_as_slice());
                    let field = ast
                        .get_unit(ty)
                        .unwrap()
                        .params_as_slice()
                        .iter()
                        .find(|p| p.ptype.typeinfo.is_paddr())
                        .expect("exactly one paddr parameter")
                        .ident();
                    return format!("{i}.{field}()");
                }
            }

            if i.has_state_references() {
                let mut path_iter = i.path_split().skip(1);
                let field = path_iter.next().unwrap();
                let slice = path_iter.next().unwrap();

                format!("{field}.extract_{slice}()")
            } else {
                i.ident().to_string()
            }
        }
        VelosiAstExpr::NumLiteral(i) => format!("{:#x}", i.val),
        VelosiAstExpr::BoolLiteral(i) => {
            if i.val {
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        VelosiAstExpr::BinOp(i) => match i.op {
            VelosiAstBinOp::LShift => {
                format!(
                    "({} << {})",
                    astexpr_to_rust_expr(&i.lhs, ident_ctx),
                    astexpr_to_rust_expr(&i.rhs, ident_ctx)
                )
            }
            VelosiAstBinOp::RShift => format!(
                "({} >> {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::And => format!(
                "({} & {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Or => format!(
                "({} | {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Xor => format!(
                "({} ^ {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Plus => format!(
                "({} + {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Minus => format!(
                "({} - {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Multiply => format!(
                "({} * {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Divide => format!(
                "({} / {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Modulo => format!(
                "({} % {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Eq => format!(
                "({} == {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Ne => format!(
                "({} != {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Lt => format!(
                "({} < {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Gt => format!(
                "({} > {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Le => format!(
                "({} <= {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Ge => format!(
                "({} >= {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Land => format!(
                "({} && {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Lor => format!(
                "({} || {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
            VelosiAstBinOp::Implies => format!(
                "(!{} || {})",
                astexpr_to_rust_expr(&i.lhs, ident_ctx),
                astexpr_to_rust_expr(&i.rhs, ident_ctx)
            ),
        },
        VelosiAstExpr::UnOp(i) => match i.op {
            VelosiAstUnOp::Not => format!("~{}", astexpr_to_rust_expr(&i.expr, ident_ctx)),
            VelosiAstUnOp::LNot => format!("!{}", astexpr_to_rust_expr(&i.expr, ident_ctx)),
        },
        VelosiAstExpr::IfElse(ite) => format!(
            "if {} {{ {} }} else {{ {} }}",
            astexpr_to_rust_expr(&ite.cond, ident_ctx),
            astexpr_to_rust_expr(&ite.then, ident_ctx),
            astexpr_to_rust_expr(&ite.other, ident_ctx)
        ),
        VelosiAstExpr::Quantifier(_) => todo!(),
        VelosiAstExpr::FnCall(_) => todo!(),
        VelosiAstExpr::Slice(_) => todo!(),
        VelosiAstExpr::Range(_) => todo!(),
    }
}

/// converts a [VelosiOperation] into a string representing the corresponding rust expression
pub fn op_to_rust_expr(
    op: &VelosiOperation,
    interface: &VelosiAstInterface,
    ast: &VelosiAst,
    method: &VelosiAstMethod,
) -> String {
    match op {
        VelosiOperation::InsertSlice(field_name, slice_name, arg) => {
            let rust_expr = opexpr_to_rust_expr(arg, ast, method);

            let field = interface.field(field_name).unwrap();
            let slice = field.slice(slice_name).unwrap();
            let rust_type = num_to_rust_type(slice.nbits());

            format!("    .insert_{slice_name}({} as {rust_type})", rust_expr)
        }
        VelosiOperation::InsertField(field, arg) => {
            format!(
                "let {field} = {}::new({});\n{field}",
                to_struct_name(field, Some("Field")),
                opexpr_to_rust_expr(arg, ast, method)
            )
        }
        VelosiOperation::ExtractSlice(field, slice) => {
            format!("let {field}_{slice} = {field}.extract_{slice}();",)
        }
        VelosiOperation::WriteAction(field) => {
            format!("self.interface.write_{field}({field});")
        }
        VelosiOperation::ReadAction(field) => {
            format!("let {field} = self.interface.read_{field}()")
        }
        VelosiOperation::GlobalBarrier => "atomic::fence(Ordering::SeqCst);".to_string(),
        VelosiOperation::Instruction(_) => todo!(),
        VelosiOperation::Return => String::new(),
    }
}

/// converts a [VelosiOpExpr] into a string representing the corresponding rust expression
fn opexpr_to_rust_expr(op: &VelosiOpExpr, ast: &VelosiAst, method: &VelosiAstMethod) -> String {
    match op {
        VelosiOpExpr::None => String::new(),
        VelosiOpExpr::Num(x) => format!("{:#x}", x),
        VelosiOpExpr::Var(x) => {
            if let VelosiAstTypeInfo::TypeRef(ty) = &method.params_map[x].ptype.typeinfo {
                let field = ast
                    .get_unit(ty)
                    .unwrap()
                    .params_as_slice()
                    .iter()
                    .find(|p| p.ptype.typeinfo.is_paddr())
                    .expect("exactly one paddr parameter")
                    .ident();
                format!("{x}.{field}()")
            } else {
                x.clone()
            }
        }
        VelosiOpExpr::Shl(x, y) => {
            format!(
                "({} << {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Shr(x, y) => {
            format!(
                "({} >> {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::And(x, y) => {
            format!(
                "({} & {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Or(x, y) => {
            format!(
                "({} | {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Add(x, y) => {
            format!(
                "({} + {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Sub(x, y) => {
            format!(
                "({} - {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Mul(x, y) => {
            format!(
                "({} * {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Div(x, y) => {
            format!(
                "({} / {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Mod(x, y) => {
            format!(
                "({} % {})",
                opexpr_to_rust_expr(x, ast, method),
                opexpr_to_rust_expr(y, ast, method)
            )
        }
        VelosiOpExpr::Flags(v, f) => format!("{v}.{f}"),
        VelosiOpExpr::Not(x) => format!("!{}", opexpr_to_rust_expr(x, ast, method)),
    }
}

/// creates a string representing the mask value
pub fn to_mask_str(m: u64, len: u64) -> String {
    match len {
        0..=8 => format!("0x{:02x}", (m & 0xff) as u8),
        9..=16 => format!("0x{:04x}", (m & 0xffff) as u16),
        17..=32 => format!("0x{:08x}", (m & 0xffffffff) as u32),
        33..=64 => format!("0x{m:016x}"),
        _ => String::from("unknown"),
    }
}

// converts a list of parameters into a comma separated argument list with the same names
pub fn params_to_args_list(params: &[Rc<VelosiAstParam>]) -> String {
    params
        .iter()
        .map(|p| p.ident_to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

// converts a list of parameters into a comma separated argument list with the same names prefixed by self
pub fn params_to_self_args_list(params: &[Rc<VelosiAstParam>]) -> String {
    params
        .iter()
        .map(|p| format!("self.{}", p.ident()))
        .collect::<Vec<_>>()
        .join(", ")
}

// converts a list of parameters into a comma separated argument list with the same names, replacing paddr
pub fn params_to_self_args_list_with_paddr(params: &[Rc<VelosiAstParam>], paddr: &str) -> String {
    params
        .iter()
        .map(|p| {
            if p.ptype.typeinfo.is_paddr() {
                paddr.to_string()
            } else {
                format!("self.{}", p.ident())
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// writes the scope to a file or to stdout
pub fn save_scope(scope: CG::Scope, outdir: &Path, name: &str) -> Result<(), VelosiCodeGenError> {
    // set the path to the file
    let file = outdir.join(format!("{name}.rs"));

    // write the file, return IOError otherwise
    fs::write(file, scope.to_string().as_bytes())?;

    Ok(())
}

/// adds the header to the file
pub fn add_header(scope: &mut CG::Scope, title: &str) {
    // set the title of the file
    // construct the license
    let mut lic = CG::License::new(title, CG::LicenseType::Mit);
    lic.add_copyright(COPYRIGHT);

    // now add the license to the scope
    scope.license(lic);

    // adding the autogenerated warning
    scope.new_comment("THIS FILE IS AUTOGENERATED BY THE VELOSIRAPTOR COMPILER");
}

pub fn add_const_def(scope: &mut CG::Scope, c: &VelosiAstConst) {
    //
    // TODO:
    //  - here we should get the type information etc...
    //  - also it would be nice to get brief descriptions of what the constant represents
    let ty = if c.value.result_type().is_boolean() {
        "bool"
    } else {
        "u64"
    };
    let val = &c.value.to_string();

    // the constant value
    let mconst = scope.new_const(c.ident(), ty, val);

    // add some documentation
    mconst.doc(vec![
        &format!("Defined constant `{}`", c.ident()),
        "",
        &format!("@loc: {}", c.loc.loc()),
    ]);

    // make it public
    mconst.vis("pub");
}

/// adds a rust constructor that is a direct translation of the vrs constructor
pub fn add_constructor(imp: &mut CG::Impl, unit_ident: &str, params: &[Rc<VelosiAstParam>]) {
    let constructor = add_constructor_signature(imp, unit_ident, params);
    constructor.line(format!("Self {{ {} }}", params_to_args_list(params)));
}

pub fn add_constructor_signature<'a>(
    imp: &'a mut CG::Impl,
    unit_ident: &str,
    params: &'a [Rc<VelosiAstParam>],
) -> &'a mut CG::Function {
    let constructor = imp
        .new_fn("new")
        .vis("pub")
        .doc(&format!(
            "Creates a new {}.\n\n# Safety\nPossibly unsafe due to being given arbitrary addresses and using them to do casts to raw pointers.",
            unit_ident
        ))
        .ret("Self")
        .set_unsafe(true);
    for p in params {
        constructor.arg(p.ident(), vrs_type_to_rust_type(&p.ptype.typeinfo));
    }
    constructor
}

pub fn import_referenced_units(scope: &mut CG::Scope, op: &VelosiAstMethod) {
    for ty in op
        .params_map
        .values()
        .filter_map(|p| match &p.ptype.typeinfo {
            VelosiAstTypeInfo::TypeRef(ty) => Some(ty),
            _ => None,
        })
    {
        scope.import("crate", &to_struct_name(ty, None));
    }
}
