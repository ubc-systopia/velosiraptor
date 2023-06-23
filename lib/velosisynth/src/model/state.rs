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
use velosiast::ast::VelosiAstState;

use super::field::{add_state_field, add_state_field_accessors};
use super::velosimodel::STATE_PREFIX;
use super::{types, utils};

// adds the state to the context
pub fn add_state_def(smt: &mut Smt2Context, prefix: &str, state: &VelosiAstState) {
    smt.section(String::from("State Fields"));

    // define a type for each state field
    for field in state.fields() {
        add_state_field(smt, prefix, field);
    }

    smt.section(String::from("State"));

    // define the data type for the state
    let mut dt = DataType::new(utils::with_prefix(prefix, STATE_PREFIX), 0);
    dt.add_comment(format!("State Definition, {}", state.loc().loc()));
    for field in state.fields() {
        dt.add_field(
            utils::with_prefix(
                prefix,
                &format!("State.{}", field.ident().split('.').last().unwrap()),
            ),
            types::field_type(prefix, STATE_PREFIX, field.ident()),
        );
    }

    // get the field accessors of the data type
    let accessors = dt.to_field_accessor();
    smt.datatype(dt);

    smt.merge(accessors);

    // add accessors for each type
    for field in state.fields() {
        add_state_field_accessors(smt, prefix, field);
    }
}
