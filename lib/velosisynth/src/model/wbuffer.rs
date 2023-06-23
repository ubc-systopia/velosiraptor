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

use smt2::{DataType, Smt2Context, Sort};
use velosiast::ast::{VelosiAstField, VelosiAstInterface};

use super::{types, velosimodel::WBUFFER_ENTRY_PREFIX};

/// adds the write buffer definitions to the model
///
/// Note: this doesn't include the write buffer actions
pub fn add_wbuffer_def(smt: &mut Smt2Context, prefix: &str, iface: &VelosiAstInterface) {
    smt.section(String::from("Write Buffer"));

    // create an enum of the different fields, used for tagging
    smt.raw(format!(
        "(declare-datatypes () (({} {})))",
        types::field_tag(),
        iface
            .fields()
            .iter()
            .map(|x| types::field_tag_enum(x.ident().as_str()))
            .collect::<Vec<_>>()
            .join(" ")
    ));

    let mut dt = DataType::new(String::from(WBUFFER_ENTRY_PREFIX), 0);
    dt.add_field(format!("{WBUFFER_ENTRY_PREFIX}.tag"), types::field_tag());
    dt.add_field(format!("{WBUFFER_ENTRY_PREFIX}.val"), types::num(prefix));

    let accessors = dt.to_field_accessor();
    smt.datatype(dt);
    smt.merge(accessors);

    smt.sort(Sort::new_def(
        types::wbuffer(),
        format!("(Seq {})", types::wbuffer_entry()),
    ));
}
