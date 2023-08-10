// VelosiParser -- a parser for the Velosiraptor Language
//
//
// MIT License
//
// Copyright (c) 2021-2023 Systopia Lab, Computer Science, University of British Columbia
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

////////////////////////////////////////////////////////////////////////////////////////////////////
// Test Utils Macros for Parsing Strings
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_compare_ok {
    ($input: expr, $parser:ident, $expected: expr) => {
        let ts = VelosiLexer::lex_string($input.to_string()).expect("lexing of input failed");
        let (rem, res) = nom::combinator::all_consuming($parser)(ts).expect("parsing failed!");
        assert!(rem.is_empty(), "did parse the entire string");
        assert_eq!(res.to_string().as_str(), $expected);
    };
    ($input: expr, $parser:ident) => {
        let ts = VelosiLexer::lex_string($input.to_string()).expect("lexing of input failed");
        let (rem, res) = nom::combinator::all_consuming($parser)(ts).expect("parsing failed!");
        assert!(rem.is_empty(), "did parse the entire string");
        assert_eq!(res.to_string().as_str(), $input);
    };
}

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_compare_fail ((
    $input: expr, $parser:ident, $expected: expr) => (
    let ts = VelosiLexer::lex_string($input.to_string()).expect("lexing of input failed");
    match  nom::combinator::all_consuming($parser)(ts) {
        Ok((_, res)) => panic!("parsing should have failed, but succeeded with {}", res),
        Err(nom::Err::Failure(e)) => {
            let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                .expect("could not string the ansi escapes");
            let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");
            assert_eq!(e.to_string(), $expected);
        }
        e => panic!("parsing should have failed, but succeeded with {}", e)
    }
));

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_check_ok ((
    $input: expr, $parser:ident) => (
    let ts = VelosiLexer::lex_string($input.to_string()).expect("lexing of input failed");
    let (rem, _) =  nom::combinator::all_consuming($parser)(ts).expect("parsing failed!");
    assert!(rem.is_empty(), "did parse the entire string");
));

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_check_fail ((
    $input: expr, $parser:ident) => (
    let ts = VelosiLexer::lex_string($input.to_string()).expect("lexing of input failed");
    assert!( nom::combinator::all_consuming($parser)(ts).is_err());
));

////////////////////////////////////////////////////////////////////////////////////////////////////
// Test Utils Macros for Parsing Files
////////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_compare_file_ok ((
    $infile: expr, $parser:ident, $expfile: expr) => (
    let ts = VelosiLexer::lex_file($infile).expect("lexing of file failed");
    let (rem, res) =  nom::combinator::all_consuming($parser)(ts).unwrap();
    let expected = fs::read_to_string($expfile).expect("could not read the exected output file");
    assert_eq!(res.to_string(), expected);
    assert!(rem.is_empty(), "did parse the entire string");
));

#[cfg(test)]
#[macro_export]
macro_rules! test_parse_and_compare_file_fail ((
    $input: expr, $parser:ident, $expfile: expr) => (
        let ts = VelosiLexer::lex_file($infile).expect("lexing of file failed");
    match  nom::combinator::all_consuming($parser)(ts) {
        Ok((_, res)) => panic!("parsing should have failed, but succeeded with {}", res),
        Err(nom::Err::Failure(e)) => {
            let plain_bytes = strip_ansi_escapes::strip(e.to_string())
                .expect("could not string the ansi escapes");
            let error_str = String::from_utf8(plain_bytes).expect("could not convert to utf8");
            let expected = fs::read_to_string($expfile).expect("could not read the exected output file");
            assert_eq!(e.to_string(), expected);
        }
        e => panic!("parsing should have failed, but succeeded with {}", e)
    }
));
