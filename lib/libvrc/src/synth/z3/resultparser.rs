// Rosette Code Generation Library
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

//! Parsing

use std::cmp::Reverse;

use super::Z3Error;

/// the used nom parsing facilities
use nom::{
    bytes::complete::tag,
    character::complete::{digit1, hex_digit1, multispace1, space1},
    combinator::all_consuming,
    multi::separated_list0,
    sequence::{delimited, preceded, tuple},
    IResult,
};

fn parse_symvar(s: &str) -> IResult<&str, (u64, u64)> {
    // (symvar!0 #x000000000000000c)
    let res = delimited(
        tag("("),
        tuple((
            delimited(tag("symvar!"), digit1, space1),
            preceded(tag("#x"), hex_digit1),
        )),
        tag(")"),
    )(s);
    match res {
        Ok((r, (n, v))) => {
            let n = n.parse::<u64>().unwrap();
            let v = u64::from_str_radix(v, 16).unwrap();
            Ok((r, (n, v)))
        }
        Err(e) => Err(e),
    }
}

/// parse and validate the result from Rosette
pub fn parse_result(res: &str) -> Result<Vec<u64>, Z3Error> {
    if res.is_empty() {
        println!("SYNTH: EMPTY OUTPUT ENCOUNTERED.\n");
        return Err(Z3Error::ResulteParseError);
    }

    let p = delimited(
        tag("("),
        separated_list0(multispace1, parse_symvar),
        tag(")\n"),
    );

    match all_consuming(p)(res) {
        Ok((_, mut symvars)) => {
            // reverse the order of the symvars, so we can pop later
            symvars.sort_by_key(|a| Reverse(a.0));
            Ok(symvars.into_iter().map(|(_, v)| v).collect())
        }
        Err(e) => {
            println!("SYNTH: ERROR PARSING OUTPUT: {:?}\n", e);
            Err(Z3Error::ResulteParseError)
        }
    }
}
