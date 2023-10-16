// Velosiraptor Code Generator
//
//
// MIT License
//
// Copyright (c) 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! C Code Generation Backend
//!
use std::collections::{HashMap, HashSet};
use std::path::Path;

use crustal as C;

use velosiast::ast::{VelosiAstMethod, VelosiAstTypeInfo, VelosiAstUnitSegment};
use velosiast::{VelosiAst, VelosiAstTypeProperty, VelosiAstUnit};
use velosicomposition::Relations;

use super::utils::{self, FieldUtils, UnitUtils};
use crate::VelosiCodeGenError;

use velosiast::VelosiAstUnitOSSpec;

pub fn generate(osspec: &VelosiAstUnitOSSpec, outdir: &Path) {
    // the code generation scope
    let mut scope = C::Scope::new();

    // constant definitions
    let title = format!("OSSPEC Definitions for `{}`", osspec.ident());
    utils::add_header(&mut scope, &title);

    let hdrguard = format!("{}_OSSPEC_H_", osspec.ident().to_uppercase());
    let guard = scope.new_ifdef(&hdrguard);
    let s = guard.guard().then_scope();

    for etype in osspec.extern_types.values() {
        let mut struct_def = C::Struct::new(etype.ident.as_str());
        if etype.fields.is_empty() {
            struct_def.new_field("__foo", C::Type::new_bool());
        } else {
            for field in &etype.fields {
                struct_def.new_field(
                    field.ident().as_str(),
                    osspec.ptype_to_ctype(&field.ptype.typeinfo, false),
                );
            }
        }
        let ty = struct_def.to_type();
        s.push_struct(struct_def);
        s.new_typedef(etype.ident.as_str(), ty);
    }

    for method in &osspec.methods {}

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Saving the file
    ////////////////////////////////////////////////////////////////////////////////////////////////

    log::debug!("saving the scope!");
    // save the scope

    let filename = format!("{}.h", osspec.ident().to_ascii_lowercase());

    scope.set_filename(&filename);
    scope.to_file(outdir, true);
}
