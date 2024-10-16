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

//! State Synthesis Module: Z3

use smt2::{DataType, Smt2Context};
use velosiast::ast::VelosiAstField;
use velosiast::ast::VelosiAstInterface;

use super::field::{add_iface_field, add_iface_field_accessors};
use super::types;
use super::utils;
use super::velosimodel::IFACE_PREFIX;

/// adds the interface definitions to the model
///
/// Note: this doesn't include the interface actions
pub fn add_interface_def(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    // add a type for each interface field
    smt.section(String::from("Interface Fields"));
    for field in iface.fields() {
        add_iface_field(smt, prefix, field);
    }

    smt.section(String::from("Interface"));

    // add a datatype for the interface
    let mut dt = DataType::new(utils::with_prefix(prefix, IFACE_PREFIX), 0);
    dt.add_comment(format!("Interface Definition, {}", iface.loc().loc()));
    for field in iface.fields() {
        dt.add_field(
            utils::with_prefix(
                prefix,
                &format!("IFace.{}", field.ident().split('.').last().unwrap()),
            ),
            types::field_type(prefix, IFACE_PREFIX, field.ident()),
        );
    }

    let accessors = dt.to_field_accessor();
    smt.datatype(dt);

    smt.merge(accessors);

    // add the field accessors
    for field in iface.fields() {
        add_iface_field_accessors(smt, prefix, field);
    }
}
