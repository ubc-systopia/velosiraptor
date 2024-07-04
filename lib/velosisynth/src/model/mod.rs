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

use smt2::{Attribute, Smt2Context, Smt2Option};
use velosiast::ast::VelosiAstUnitSegment;

pub mod consts;
pub mod expr;
pub mod field;
pub mod flags;
pub mod interface;
pub mod method;
pub mod state;
pub mod types;
mod utils;
pub mod velosimodel;
pub mod wbuffer;

pub fn create(unit: &VelosiAstUnitSegment, mem_model: bool) -> Smt2Context {
    let mut smt = Smt2Context::new();

    // adding general type definitions
    types::add_type_defs(&mut smt, unit.ident(), unit.inbitwidth, unit.outbitwidth);

    // TODO: adding global constants

    // adding the model
    consts::add_consts(&mut smt, unit.ident(), Box::new(unit.consts()));
    if let Some(flags) = &unit.flags {
        flags::add_flags(&mut smt, unit.ident(), flags);
    }

    state::add_state_def(&mut smt, unit.ident(), &unit.state);
    interface::add_interface_def(&mut smt, unit.ident(), &unit.interface);
    if mem_model {
        wbuffer::add_wbuffer_def(&mut smt, unit.ident(), &unit.interface);
    }
    velosimodel::add_model_def(&mut smt, unit, mem_model);

    // valid needs to be defined first so that it can be used in the other method assumptions
    method::add_methods(
        &mut smt,
        unit.ident(),
        Box::new(unit.get_method("valid").into_iter()),
    );
    method::add_methods(
        &mut smt,
        unit.ident(),
        Box::new(unit.methods().filter(|m| m.ident.as_str() != "valid")),
    );

    smt
}

/// creates the common options and definitions used across all unit models
pub fn prelude() -> Smt2Context {
    let mut smt = Smt2Context::new();

    // set the options
    smt.set_option(Smt2Option::ProduceUnsatCores(true));
    // smt.set_option(Smt2Option::RandomSeed(0x533d));

    let options = vec![
        "smt.arith.nl false",
        "parallel.enable true",
        "parallel.threads.max 2",
        "rewriter.bv_le_extra true",
        "rewriter.bv_not_simpl true",
        "rewriter.cache_all true",
        "push_ite_bv true",
        "pi.use_database true",
        "arith.auto_config_simplex true",
        "arith.solver 2"
    ];

    for o in options {
        smt.set_option(Smt2Option::Attribute(Attribute::new(o.into())));
    }

    smt
}
