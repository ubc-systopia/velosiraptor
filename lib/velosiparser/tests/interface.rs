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

/// test basic interface definition
#[test]
fn interface_basic_def() {
    let vrs = Path::new("tests/vrs/interface/interface_00_basic_def.vrs");
    let exp = Path::new("tests/vrs/interface/interface_00_basic_def_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// tests the bitslices
#[test]
fn interface_bitslices_def() {
    let vrs = Path::new("tests/vrs/interface/interface_01_bitslices_def.vrs");
    let exp = Path::new("tests/vrs/interface/interface_01_bitslices_def_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// tests the bitslices
#[test]
fn interface_actions_def() {
    let vrs = Path::new("tests/vrs/interface/interface_02_actions_def.vrs");
    let exp = Path::new("tests/vrs/interface/interface_02_actions_def_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Err Tests
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test registers not properly separated
#[test]
fn interface_err_register_defs_not_separated() {
    let vrs = Path::new("tests/vrs/interface/interface_03_register_not_separated.vrs");
    let exp = Path::new("tests/vrs/interface/interface_03_register_not_separated_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}

#[test]
fn interface_err_register_defs_wrong_separator() {
    let vrs = Path::new("tests/vrs/interface/interface_04_register_wrong_separator.vrs");
    let exp = Path::new("tests/vrs/interface/interface_04_register_wrong_separator_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}

#[test]
fn interface_err_empty_register() {
    let vrs = Path::new("tests/vrs/interface/interface_05_empty_register.vrs");
    let exp = Path::new("tests/vrs/interface/interface_05_empty_register_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}
