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

// our library
mod utils;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Success Cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test empty osspec
#[test]
fn osspec_ok_00_simple() {
    let vrs = Path::new("tests/vrs/osspec/osspec_ok_00_empty.vrs");
    let exp = Path::new("tests/vrs/osspec/osspec_ok_00_empty_expected.txt");

    utils::check_parse_file_ok_strict(&vrs, Some(&exp));
}

/// test os spec with external function
#[test]
fn osspec_ok_01_extern_fn() {
    let vrs = Path::new("tests/vrs/osspec/osspec_ok_01_extern_fn.vrs");
    let exp = Path::new("tests/vrs/osspec/osspec_ok_01_extern_fn_expected.txt");

    utils::check_parse_file_ok_strict(&vrs, Some(&exp));
}

/// test os spec with external function
#[test]
fn osspec_ok_02_map_fn() {
    let vrs = Path::new("tests/vrs/osspec/osspec_ok_02_map.vrs");
    let exp = Path::new("tests/vrs/osspec/osspec_ok_02_map_expected.txt");

    utils::check_parse_file_ok_strict(&vrs, Some(&exp));
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Error cases
////////////////////////////////////////////////////////////////////////////////////////////////////

/// test os spec with external function
#[test]
fn osspec_err_00_synth_abstract_fn() {
    let vrs = Path::new("tests/vrs/osspec/osspec_err_00_synth_abstract_fn.vrs");
    let exp = Path::new("tests/vrs/osspec/osspec_err_00_synth_abstract_fn_expected.txt");

    utils::check_parse_file_fail(&vrs, Some(&exp));
}
