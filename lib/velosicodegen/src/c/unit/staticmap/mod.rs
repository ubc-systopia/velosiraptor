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

use crustal as C;

use velosiast::{VelosiAst, VelosiAstStaticMap, VelosiAstUnitStaticMap};
use velosicomposition::Relations;

use super::utils::{self};
use crate::VelosiCodeGenError;

mod explicit_map;
mod listcomp_map;

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

    s.new_comment(" --------------------------------- Constants ---------------------------------");

    // adding the unit constants
    add_unit_constants(s, unit);

    match &unit.map {
        VelosiAstStaticMap::ListComp(lc_map) => {
            listcomp_map::generate(s, unit, lc_map, relations, osspec, outdir);
        }
        VelosiAstStaticMap::Explicit(ex_map) => {
            explicit_map::generate(s, unit, ex_map, relations, osspec, outdir);
        }
        VelosiAstStaticMap::None(_) => { /* no-op */ }
    }

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
