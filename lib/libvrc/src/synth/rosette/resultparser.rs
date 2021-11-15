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

/// the used nom parsing facilities
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, digit1, hex_digit1, newline, space0, space1},
    combinator::{all_consuming, opt, recognize},
    multi::many1,
    sequence::{delimited, preceded, terminated, tuple},
    IResult,
};

/// defines an argumetn for an operation
#[derive(Debug)]
pub enum OpArg {
    /// a constant number
    Num(u64),
    /// a variable
    Var(String),
    /// no argument for this operation
    None,
}

/// defines an operation
#[derive(Debug)]
pub struct Operation {
    /// the name of the operation as a string
    pub op: String,
    /// the arguments for this operation
    pub arg: OpArg,
}

impl Operation {
    /// creates a new operation
    pub fn new(op: &str, arg: OpArg) -> Self {
        Operation {
            op: String::from(op),
            arg,
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////
// Result Parsing
///////////////////////////////////////////////////////////////////////////////////////////////

/// parser to recognize a bitvector constaint `(bv #x1 64)`
fn parse_oparg_bv(s: &str) -> IResult<&str, OpArg> {
    let bv = tuple((tag("(bv"), space1));
    let width = tuple((space1, digit1, tag(")")));
    let value = preceded(tag("#x"), hex_digit1);

    let (r, n) = delimited(bv, value, width)(s)?;
    match u64::from_str_radix(n, 16) {
        Ok(i) => Ok((r, OpArg::Num(i))),
        Err(_) => panic!("number {} not parsable as hex", n),
    }
}

/// parser to recognize a sybolic variable  e.g., `pa`
fn parse_oparg_var(s: &str) -> IResult<&str, OpArg> {
    let (r, n) = alphanumeric1(s)?;
    Ok((r, OpArg::Var(String::from(n))))
}

/// parser to recognize a single operation `(op arg)`
fn parse_op(s: &str) -> IResult<&str, Operation> {
    // the op name is alphanumeric + '_'
    let opname = recognize(many1(alt((alphanumeric1, tag("_")))));
    // the opargs are bv, var, or nothing

    let opargs = opt(alt((parse_oparg_bv, parse_oparg_var)));
    // the operation is then the name, followed by maybe arguments

    let op = tuple((opname, preceded(space0, opargs)));

    // the operation is delimted in parenthesis
    let (r, (n, a)) = delimited(tag("("), op, tag(")"))(s)?;

    // get the argument, or set it to None if there was none
    let arg = a.unwrap_or(OpArg::None);
    let op = Operation::new(n, arg);
    Ok((r, op))
}

/// parser to recognize a sequence `(Seq Op [Seq | Res])`
fn parse_seq(s: &str) -> IResult<&str, Vec<Operation>> {
    // parse the operation of the sequence
    let (s1, op) = preceded(tag("(Seq "), parse_op)(s)?;

    // the next token is either another sequence or a result
    let next = preceded(space1, alt((parse_seq, parse_res)));

    // parse the remainder of the sequence, close by parenthesis
    let (s2, rops) = terminated(next, tag(")"))(s1)?;

    // construct the sequence
    let mut ops = vec![op];
    ops.extend(rops);

    // all right, we have a vector of operations
    Ok((s2, ops))
}

/// parser to recognize the return statement `(Return)`
fn parse_res(s: &str) -> IResult<&str, Vec<Operation>> {
    // just recognize a `(Return)`
    let (r, _) = delimited(tag("("), tag("Return"), tag(")"))(s)?;
    Ok((r, vec![Operation::new("return", OpArg::None)]))
}

/// parse and validate the result from Rosette
pub fn parse_result(output: &str) -> Vec<Operation> {
    // we want to consume all of the output on a single line.
    let ops = match all_consuming(terminated(parse_seq, newline))(output) {
        Ok((_, v)) => v,
        Err(e) => panic!("parser did not finish: {:?}", e),
    };

    ops
}

#[test]
fn test_parser() {
    let s = "(Seq (Op_Iface_sz_bytes_Insert (bv #x4000000000000000 64)) (Seq (Op_Iface_sz_WriteAction) (Seq (Op_Iface_flags_present_Insert (bv #x0000000000000001 64)) (Seq (Op_Iface_flags_WriteAction) (Seq (Op_Iface_address_base_Insert pa) (Seq (Op_Iface_address_WriteAction) (Return)))))))\n";
    parse_result(s);
}
