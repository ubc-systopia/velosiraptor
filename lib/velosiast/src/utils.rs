// VelosiAst -- a Ast for the Velosiraptor Language
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

//! Utils Module

use std::collections::HashMap;
use std::rc::Rc;

use velosiparser::VelosiTokenStream;

use crate::ast::{
    VelosiAstExpr, VelosiAstFieldSlice, VelosiAstIdentifier, VelosiAstInterfaceAction,
    VelosiAstNode, VelosiAstParam, VelosiAstStaticMapElement,
};
use crate::error::{
    VelosiAstErrBuilder, VelosiAstErrDoubleDef, VelosiAstErrUndef, VelosiAstIssues,
};
use crate::SymbolTable;

/// checks if the identifier has snake case
pub fn check_upper_case(issues: &mut VelosiAstIssues, id: &VelosiAstIdentifier) {
    let name = id.ident();
    let allupper = name
        .chars()
        .all(|x| x.is_ascii_uppercase() || !x.is_alphabetic());
    if !allupper {
        let msg = format!("identifier `{name}` should have an upper case name");
        let hint = format!(
            "convert the identifier to upper case (notice the capitalization): `{}`",
            name.to_ascii_uppercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(id.loc.clone())
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_snake_case(issues: &mut VelosiAstIssues, id: &VelosiAstIdentifier) {
    let name = id.ident();
    let allupper = name
        .chars()
        .all(|x| x.is_ascii_lowercase() || !x.is_alphabetic());
    if !allupper {
        let msg = format!("identifier `{name}` should have a snake case name");
        let hint = format!(
            "convert the identifier to lowercase (notice the snake_case): `{}`",
            name.to_ascii_lowercase()
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(id.loc.clone())
            .build();

        issues.push(err);
    }
}

pub fn check_camel_case(issues: &mut VelosiAstIssues, id: &VelosiAstIdentifier) {
    let name = id.ident();

    let mut has_issue = false;
    let mut prev_not_alnum = true;
    let mut camel_case = String::with_capacity(name.len());
    for (i, char) in name.chars().enumerate() {
        if i == 0 {
            has_issue = char.is_ascii_lowercase() || !char.is_alphabetic()
        }

        if !char.is_alphanumeric() {
            prev_not_alnum = true;
            has_issue = true;
        } else if prev_not_alnum {
            prev_not_alnum = false;
            camel_case.push(char.to_ascii_uppercase());
        } else {
            camel_case.push(char);
        }
    }

    if has_issue {
        let msg = format!("identifier `{name}` should have a camel case name");
        let hint = format!(
            "convert the identifier to lowercase (notice the CamelCase): `{}`",
            camel_case
        );
        let err = VelosiAstErrBuilder::warn(msg)
            .add_hint(hint)
            .add_location(id.loc.clone())
            .build();

        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_type_exists(
    issues: &mut VelosiAstIssues,
    st: &SymbolTable,
    id: &VelosiAstIdentifier,
) -> bool {
    let name = id.path();
    if let Some(s) = st.lookup(name) {
        match s.ast_node {
            // there is a unit with that type, so we're good
            VelosiAstNode::Unit(_) => false,
            VelosiAstNode::ExternType(_) => true,
            _ => {
                // report that there was a mismatching type
                let err = VelosiAstErrUndef::from_ident_with_other(id, s.loc().clone());
                issues.push(err.into());
                false
            }
        }
    } else {
        // there is no such type, still create the node and report the issue
        let err = VelosiAstErrUndef::from_ident(id);
        issues.push(err.into());
        false
    }
}

/// checks whether the identifier is in snake_case
pub fn check_param_exists(
    issues: &mut VelosiAstIssues,
    st: &SymbolTable,
    id: &VelosiAstIdentifier,
) {
    let name = id.path();
    if let Some(s) = st.lookup(name) {
        match s.ast_node {
            // there is a unit with that type, so we're good
            VelosiAstNode::Param(_) => (),
            _ => {
                // report that there was a mismatching type
                let err = VelosiAstErrUndef::from_ident_with_other(id, s.loc().clone());
                issues.push(err.into());
            }
        }
    } else {
        // there is no such type, still create the node and report the issue
        let err = VelosiAstErrUndef::from_ident(id);
        issues.push(err.into());
    }
}

/// checks whether the identifier is in snake_case
pub fn check_addressing_width(issues: &mut VelosiAstIssues, w: u64, loc: VelosiTokenStream) {
    if w > 64 {
        let msg = "unsupported addressing width: exceeds maximum addressing size of 64 bits";
        let hint = "reduce the addressing width to 64 bits or less";
        let err = VelosiAstErrBuilder::err(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc.clone())
            .build();
        issues.push(err);
    }

    if w == 0 {
        let msg = "unsupported addressing width: addressing size is zero";
        let hint = "increase the adressing width";
        let err = VelosiAstErrBuilder::err(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc.clone())
            .build();
        issues.push(err);
    }

    if w < 8 {
        let msg = "unusual addressing width: addressing size is very small";
        let hint = "consider increase the adressing width";
        let err = VelosiAstErrBuilder::warn(msg.to_string())
            .add_hint(hint.to_string())
            .add_location(loc)
            .build();
        issues.push(err);
    }
}

/// checks whether the identifier is in snake_case
pub fn check_field_size(
    issues: &mut VelosiAstIssues,
    size: u64,
    size_loc: &VelosiTokenStream,
) -> u64 {
    if ![1, 2, 4, 8].contains(&size) {
        if [16, 32, 64].contains(&size) {
            let bytes = size / 8;
            let msg = format!("Size in bits given, bytes expected. Converting to {bytes} bytes.");
            let hint = "Change the size information to one of 1, 2, 4, 8.";
            let err = VelosiAstErrBuilder::warn(msg)
                .add_hint(hint.to_string())
                .add_location(size_loc.clone())
                .build();
            issues.push(err);
            return bytes;
        } else {
            let msg = format!("Unsupported size of the memory field: {size}");
            let hint = "Change the size information to one of 1, 2, 4, 8.";
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint.to_string())
                .add_location(size_loc.clone())
                .build();
            issues.push(err);
        }
    }
    size
}

pub fn slice_overlap_check(
    issues: &mut VelosiAstIssues,
    sizebits: u64,
    slices: &[Rc<VelosiAstFieldSlice>],
) {
    let mut bits: Vec<Option<Rc<VelosiAstFieldSlice>>> = vec![None; sizebits as usize];
    for slice in slices {
        for (i, e) in bits
            .iter_mut()
            .enumerate()
            .take(slice.end as usize)
            .skip(slice.start as usize)
        {
            // overflow captured at another place
            if i >= sizebits as usize {
                break;
            }
            if let Some(s) = e {
                let msg = format!("Field slices overlap at bit {i}");
                let hint = format!("This slice overlaps with slice `{}`", s.ident);
                let related = "This is the slice that overlaps with.";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint)
                    .add_location(slice.loc.clone())
                    .add_related_location(related.to_string(), s.loc.clone())
                    .build();
                issues.push(err);
                break;
            }
            *e = Some(slice.clone());
        }
    }
}

pub fn actions_conflict_check(issues: &mut VelosiAstIssues, actions: &[VelosiAstInterfaceAction]) {
    let mut dst: Vec<(&str, &VelosiTokenStream)> = Vec::new();

    for action in actions {
        let ident = match action.dst.as_ref() {
            VelosiAstExpr::IdentLiteral(e) => e.ident(),
            VelosiAstExpr::Slice(e) => e.ident(),
            _ => "",
        };

        if ident.is_empty() {
            continue;
        }

        for d in dst.iter() {
            if d.0 == ident {
                // they are equial, we have a conflict
                let msg = format!("Conflicting action destination `{}`", action.dst);
                let hint = "this destination of the action";
                let related = "this is the other action that uses the same destination";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(action.loc.clone())
                    .add_related_location(related.to_string(), d.1.clone())
                    .build();
                issues.push(err);
            } else if d.0.starts_with(ident) || ident.starts_with(d.0) {
                // the new one is the full field, or the old one is the full field
                let msg = format!(
                    "Conflicting action destination `{}` (full field)",
                    action.dst
                );
                let hint = "this destination of the action";
                let related = "this is the action that overlaps";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(action.loc.clone())
                    .add_related_location(related.to_string(), d.1.clone())
                    .build();
                issues.push(err);
            }
        }

        dst.push((ident, &action.loc));
    }
}

pub fn check_fn_call_args(
    issues: &mut VelosiAstIssues,
    _st: &SymbolTable,
    params: &[Rc<VelosiAstParam>],
    args: &[Rc<VelosiAstExpr>],
    callsite: &VelosiTokenStream,
) {
    let nparam = params.len();
    let nargs = args.len();

    if nparam != nargs {
        let msg = format!(
            "this function takes {} argument{} but {} argument{} supplied",
            nparam,
            if nparam == 1 { "" } else { "s" },
            nargs,
            if nargs == 1 { "s were" } else { " was" }
        );

        let (hint, loc) = if nparam < nargs {
            // too many arguments
            let hint = format!(
                "remove the {} unexpected argument{}",
                nargs - nparam,
                if nargs - nparam == 1 { "" } else { "s" }
            );

            let mut loc = if nparam == 0 {
                callsite.clone()
            } else {
                args[nparam].loc().clone()
            };

            loc.expand_until_end(args[nargs - 1].loc());
            (hint, loc)
        } else {
            // to few arguments
            let hint = format!(
                "add the {} missing argument{}",
                nparam - nargs,
                if nparam - nargs == 1 { "" } else { "s" }
            );
            let loc = if nargs == 0 {
                callsite.clone()
            } else {
                args[nargs - 1].loc().clone()
            };

            (hint, loc)
        };

        let err = VelosiAstErrBuilder::err(msg)
            .add_hint(hint)
            .add_location(loc)
            //.add_related_location("parameters defined here".to_string(), m.loc.clone())
            .build();
        issues.push(err);
    }

    for (i, arg) in args.iter().enumerate() {
        if i >= nparam {
            let msg = "unexpected argument";
            let hint = "remove this argument to the function call";
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint.to_string())
                .add_location(arg.loc().clone())
                .build();
            issues.push(err);
            continue;
        }

        let param = &params[i];
        if !param.ptype.typeinfo.compatible(arg.result_type()) {
            let msg = "mismatched types";
            let hint = format!("expected {}, found {}", param.ptype, arg.result_type());
            let err = VelosiAstErrBuilder::err(msg.to_string())
                .add_hint(hint)
                .add_location(arg.loc().clone())
                .build();
            issues.push(err);
        }
    }
}

pub fn check_layout_qauality(
    issues: &mut VelosiAstIssues,
    global: &[Rc<VelosiAstFieldSlice>],
    current: &[Rc<VelosiAstFieldSlice>],
) {
    let global_num_elements = global.len();
    let current_num_elements = current.len();

    if global_num_elements != current_num_elements && current_num_elements != 0 {
        let (hint, loc) = if global_num_elements < current_num_elements {
            // too many slices
            let hint = format!(
                "remove the {} unexpected argument{}",
                current_num_elements - global_num_elements,
                if current_num_elements - global_num_elements == 1 {
                    ""
                } else {
                    "s"
                }
            );

            let mut loc = current[global_num_elements].loc.clone();
            loc.expand_until_end(&current[current_num_elements - 1].loc);
            (hint, loc)
        } else {
            // to few slices
            let hint = format!(
                "add the {} missing slices{}",
                global_num_elements - current_num_elements,
                if global_num_elements - current_num_elements == 1 {
                    ""
                } else {
                    "s"
                }
            );

            let loc = current[current_num_elements - 1].loc.clone();

            (hint, loc)
        };
        let msg = "number of slices does not match";
        let err = VelosiAstErrBuilder::err(msg.to_string())
            .add_hint(hint)
            .add_location(loc)
            //.add_related_location("parameters defined here".to_string(), m.loc.clone())
            .build();
        issues.push(err);
    }

    for i in 0..std::cmp::max(global_num_elements, current_num_elements) {
        let msg = "field layout mismatch";
        let mut err = VelosiAstErrBuilder::err(msg.to_string());

        if i >= global_num_elements {
            // too many slices in the current
            let hint = "remove this slice from the field layout.";
            let loc = current[i].loc.clone();

            err.add_hint(hint.to_string()).add_location(loc);
            issues.push(err.build());
            continue;
        }

        if i >= current_num_elements {
            // missing slices in the current
            let mut loc = current[0].loc.clone();
            loc.expand_until_end(&current[current_num_elements - 1].loc);

            let related = "add this slice to the layout";
            err.add_location(loc)
                .add_related_location(related.to_string(), global[i].loc.clone());
            issues.push(err.build());
            continue;
        }

        let mut err = VelosiAstErrBuilder::err(String::new());

        // same amount of slices in the current
        if global[i].ident() != current[i].ident() {
            err.add_message("field slice identifier mismatch.".to_string());
            err.add_hint(format!("expected slice with name {}", global[i].ident()));
            err.add_location(current[i].loc.clone());
            if global[i].ident().as_str() != "_val" {
                err.add_related_location(
                    "this is the definition".to_string(),
                    global[i].loc.clone(),
                );
            }
        } else if global[i].start != current[i].start {
            err.add_message("start bit offset mismatch.".to_string());
            err.add_location(current[i].loc.clone());
            if global[i].ident().as_str() != "_val" {
                err.add_hint(format!("expected start bit {}", global[i].start));
                err.add_related_location(
                    "this is the definition".to_string(),
                    global[i].loc.clone(),
                );
            }
        } else if global[i].end != current[i].end {
            err.add_message("end bit offset mismatch.".to_string());
            err.add_location(current[i].loc.clone());
            if global[i].ident().as_str() != "_val" {
                err.add_hint(format!("change this bit {}", global[i].end));
                err.add_related_location(
                    "this is the definition".to_string(),
                    global[i].loc.clone(),
                );
            }
        } else {
            continue;
        };

        issues.push(err.build());
    }
}

pub fn check_element_ranges(
    issues: &mut VelosiAstIssues,
    st: &SymbolTable,
    elms: &[VelosiAstStaticMapElement],
) {
    // nothing to be done
    if elms.is_empty() {
        return;
    }

    let mut ranges: Vec<(usize, u64, u64)> = Vec::new();

    let mut last_range = 0;
    for (i, e) in elms.iter().enumerate() {
        // the unit end offset is the last address that is of this range when adding to the
        // start, the units will have an input range of [0, end_offset] (including)
        let mut unit_end_offset = 0xffff_ffff_ffff_ffff;
        if let Some(u) = st.lookup(e.dst.path()) {
            if let VelosiAstNode::Unit(u) = &u.ast_node {
                let inputbits = u.input_bitwidth();
                if inputbits < 64 {
                    unit_end_offset = (1u64 << inputbits) - 1;
                }
            }
        }

        // the range size is
        let mut rangesize = unit_end_offset;
        if let Some(range) = &e.src {
            // check if the range is const
            if !range.is_const() {
                let msg = format!("evaluated source range `{range}` is not constant");
                let hint = "convert this to a constant expression";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(range.loc.clone())
                    .build();
                issues.push(err);
            }
            // get the const base limit, otherwise assume full range
            let (start, end) = range
                .try_get_start_limit()
                .unwrap_or((0, 0xffff_ffff_ffff_ffff));

            rangesize = std::cmp::min(rangesize, end - start);

            // figure out power of two!
            if (rangesize & (rangesize - 1)) != 0 {
                let msg = format!("Range has not a power of two size ({rangesize})");
                let hint = "Change the range to be a power of two";
                let err = VelosiAstErrBuilder::err(msg.to_string())
                    .add_hint(hint.to_string())
                    .add_location(range.loc.clone())
                    .build();
                issues.push(err);
            }

            // check if range size <= unitsize
            if rangesize > unit_end_offset {
                let msg = format!("evaluated source range `{range}` exceeds input unit size");
                let hint = "reduce the spanned input range here";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(range.loc.clone())
                    .build();
                issues.push(err);
            }

            ranges.push((i, start, end));
            last_range = end;
        } else if unit_end_offset <= u64::MAX - last_range {
            ranges.push((i, last_range, last_range + unit_end_offset));
            last_range += unit_end_offset;
        } else {
            ranges.push((i, last_range, u64::MAX));
            last_range = u64::MAX;
        }

        if let Some(offset) = &e.offset {
            // not constant
            if !offset.is_const_expr() {
                let msg = format!("evaluated offset expression `{offset}` is not constant");
                let hint = "convert this to a constant expression";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(offset.loc().clone())
                    .build();
                issues.push(err);
            }
            let offestval = 0;
            // exceeds the destination size
            if offestval + rangesize > unit_end_offset {
                let msg = format!(
                    "offset exceeds unit size. maximum offset is {} ",
                    unit_end_offset - rangesize
                );
                let hint = "reduce this offset";
                let err = VelosiAstErrBuilder::err(msg)
                    .add_hint(hint.to_string())
                    .add_location(offset.loc().clone())
                    .build();
                issues.push(err);
            }
        }
    }

    // should not have lost any of the ranges
    assert_eq!(ranges.len(), elms.len());

    // sort the ranges
    ranges.sort_by_key(|e| e.1);

    let mut iter = ranges.iter();
    let (idx, start, end) = iter.next().unwrap();

    let mut prev_idx = *idx;
    let mut prev_end = *end;
    let mut prev_start = *start;

    for (idx, start, end) in iter {
        // this doesn't find all the previous overlaps, but catches at least one
        if *start >= *end {
            let msg = format!("range overlap: range 0x{prev_start:x}..0x{prev_end:x} overlaps with range 0x{start:x}..0x{end:x}  (entries {prev_idx} andd {idx})");
            let hint = format!("this entry here (var = {idx})");
            let related = format!("this is the overlapping entry (var = {idx})");
            let err = VelosiAstErrBuilder::err(msg)
                .add_hint(hint)
                .add_location(elms[*idx].loc.clone())
                .add_related_location(related, elms[prev_idx].loc.clone())
                .build();
            issues.push(err);
            break;
        }
        if *end > prev_end {
            prev_end = *end;
            prev_idx = *idx;
            prev_start = *start;
        }
    }
}

pub fn check_param_double_definitions(issues: &mut VelosiAstIssues, params: &[Rc<VelosiAstParam>]) {
    let mut params_map: HashMap<&str, &Rc<VelosiAstParam>> = HashMap::new();
    for p in params.iter() {
        let p_key = p.ident().as_str();
        if let Some(param) = params_map.get(p_key) {
            issues.push(
                VelosiAstErrDoubleDef::new(p.ident().clone(), param.loc.clone(), p.loc.clone())
                    .into(),
            );
        } else {
            params_map.insert(p_key, p);
        }
    }
}
