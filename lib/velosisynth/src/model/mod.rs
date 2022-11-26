// Velosiraptor Synthesizer
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

use smt2::{Smt2Context, Smt2Option};
use velosiast::ast::VelosiAstUnitSegment;

pub mod consts;
pub mod expr;
pub mod field;
pub mod flags;
pub mod interface;
pub mod method;
pub mod state;
pub mod types;
pub mod velosimodel;

pub fn create(unit: &VelosiAstUnitSegment) -> Smt2Context {
    let mut smt = Smt2Context::new();

    // set the options
    smt.set_option(Smt2Option::ProduceUnsatCores(true));

    // adding general type definitions
    types::add_type_defs(&mut smt, unit.inbitwidth, unit.outbitwidth);

    // TODO: adding global constants

    // adding the model
    consts::add_consts(&mut smt, unit.ident_as_str(), unit.consts.as_slice());
    if let Some(flags) = &unit.flags {
        flags::add_flags(&mut smt, unit.ident_as_str(), flags);
    }

    state::add_state_def(&mut smt, &unit.state);
    interface::add_interface_def(&mut smt, &unit.interface);
    velosimodel::add_model_def(&mut smt, unit);
    method::add_methods(&mut smt, unit.methods.as_slice());

    smt
}
