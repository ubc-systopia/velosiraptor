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
use std::fs::{self};

use std::path::Path;

// our library
use velosiparser::{VelosiParser, VelosiParserError};

mod utils;

/// test global flags definition
#[test]
fn flags_global_def() {
    let vrs = Path::new("tests/vrs/flags/flags_00_global.vrs");
    let exp = Path::new("tests/vrs/flags/flags_00_global_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// Test unit flags definition
#[test]
fn flags_unit_def() {
    let vrs = Path::new("tests/vrs/flags/flags_01_unit.vrs");
    let exp = Path::new("tests/vrs/flags/flags_01_unit_expected.txt");
    utils::check_parse_ok(vrs, None);
    utils::check_parse_ok(vrs, Some(exp));
}

/// test wrong syntax
#[test]
fn flags_gobal_eq_fail() {
    let vrs = Path::new("tests/vrs/flags/flags_02_global_eq.vrs");
    let exp = Path::new("tests/vrs/flags/flags_02_global_eq_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}

/// test wrong syntax 2
#[test]
fn flags_gobal_body_fail() {
    let vrs = Path::new("tests/vrs/flags/flags_03_global_body.vrs");
    let exp = Path::new("tests/vrs/flags/flags_03_global_body_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}

/// test wrong syntax 2
#[test]
fn flags_gobal_flags_fail() {
    let vrs = Path::new("tests/vrs/flags/flags_04_global_flags.vrs");
    let exp = Path::new("tests/vrs/flags/flags_04_global_flags_expected.txt");
    utils::check_parse_fail(vrs, None);
    utils::check_parse_fail(vrs, Some(exp));
}
