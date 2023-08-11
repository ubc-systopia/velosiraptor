// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021, 2022 Systopia Lab, Computer Science, University of British Columbia
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

//! # VelosiParser Tests: Example Specs

// std includes
use std::path::Path;

mod utils;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Ok Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test basic method definition
#[test]
fn methods_simple() {
    let vrs = Path::new("tests/vrs/methods/methods_00_simple.vrs");
    let exp = Path::new("tests/vrs/methods/methods_00_simple_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// test post and pre-condition definition
#[test]
fn methods_pre_post_conditions() {
    let vrs = Path::new("tests/vrs/methods/methods_01_pre_post_conditions.vrs");
    let exp = Path::new("tests/vrs/methods/methods_01_pre_post_conditions_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// test synth and abstract definitions
#[test]
fn methods_synth_abstract() {
    let vrs = Path::new("tests/vrs/methods/methods_02_synth_abstract.vrs");
    let exp = Path::new("tests/vrs/methods/methods_02_synth_abstract_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// test basic interface definition
#[test]
fn methods_decorators() {
    let vrs = Path::new("tests/vrs/methods/methods_03_decorators.vrs");
    let exp = Path::new("tests/vrs/methods/methods_03_decorators_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// test basic interface definition
#[test]
fn method_err_empty_body() {
    let vrs = Path::new("tests/vrs/methods/methods_04_empty_body.vrs");
    let exp = Path::new("tests/vrs/methods/methods_04_empty_body_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}

/// test basic interface definition
#[test]
fn method_err_arguments_no_types() {
    let vrs = Path::new("tests/vrs/methods/methods_05_arguments_no_types.vrs");
    let exp = Path::new("tests/vrs/methods/methods_05_arguments_no_types_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}
