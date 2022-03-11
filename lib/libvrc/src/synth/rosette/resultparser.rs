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

use crate::synth::{OpExpr, Operation};

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

///////////////////////////////////////////////////////////////////////////////////////////////
// Result Parsing
///////////////////////////////////////////////////////////////////////////////////////////////

/// parser to recognize a bitvector constaint `(bv #x1 64)`
fn parse_oparg_bv(s: &str) -> IResult<&str, OpExpr> {
    let bv = tuple((tag("(bv"), space1));
    let width = tuple((space1, digit1, tag(")")));
    let value = preceded(tag("#x"), hex_digit1);

    let (r, n) = delimited(bv, value, width)(s)?;
    match u64::from_str_radix(n, 16) {
        Ok(i) => Ok((r, OpExpr::Num(i))),
        Err(_) => panic!("number {} not parsable as hex", n),
    }
}

/// parser to recognize a sybolic variable  e.g., `pa`
fn parse_oparg_var(s: &str) -> IResult<&str, OpExpr> {
    let (r, n) = alphanumeric1(s)?;
    Ok((r, OpExpr::Var(String::from(n))))
}

/// parses a bitvector operator argument `(bvshl va size)`
fn parse_oparg_bvop(s: &str) -> IResult<&str, OpExpr> {
    // the possible bi
    let bvop = alt((
        tag("bvshl"),
        tag("bvlshr"),
        tag("bvadd"),
        tag("bvsub"),
        tag("bvand"),
        tag("bvor"),
        tag("bvmul"),
        tag("bvudiv"),
        tag("bvurem"),
    ));

    let bvop_parser = tuple((
        bvop,
        space1,
        alt((parse_oparg_bv, parse_oparg_var)),
        space1,
        alt((parse_oparg_bv, parse_oparg_var)),
    ));
    let (r, (o, _, a1, _, a2)) = delimited(tag("("), bvop_parser, tag(")"))(s)?;

    match o {
        "bvshl" => Ok((r, OpExpr::Shl(Box::new(a1), Box::new(a2)))),
        "bvlshr" => Ok((r, OpExpr::Shr(Box::new(a1), Box::new(a2)))),
        "bvadd" => Ok((r, OpExpr::Add(Box::new(a1), Box::new(a2)))),
        "bvsub" => Ok((r, OpExpr::Sub(Box::new(a1), Box::new(a2)))),
        "bvand" => Ok((r, OpExpr::And(Box::new(a1), Box::new(a2)))),
        "bvor" => Ok((r, OpExpr::Or(Box::new(a1), Box::new(a2)))),
        "bvmul" => Ok((r, OpExpr::Mul(Box::new(a1), Box::new(a2)))),
        "bvudiv" => Ok((r, OpExpr::Div(Box::new(a1), Box::new(a2)))),
        "bvurem" => Ok((r, OpExpr::Mod(Box::new(a1), Box::new(a2)))),
        _ => panic!("unexpected operator {}", o),
    }
}

/// parser to recognize a single operation `(op arg)`
fn parse_op(s: &str) -> IResult<&str, Operation> {
    // the op name is alphanumeric + '_'
    let opname = recognize(many1(alt((alphanumeric1, tag("_"), tag("-")))));

    // the opargs are bv, var, or nothing
    let opargs = opt(alt((parse_oparg_bv, parse_oparg_var, parse_oparg_bvop)));

    // the operation is then the name, followed by maybe arguments
    let op = tuple((opname, preceded(space0, opargs)));

    // the operation is delimted in parenthesis
    let (r, (n, a)) = delimited(tag("("), op, tag(")"))(s)?;

    // get the argument, or set it to None if there was none
    let arg = a.unwrap_or(OpExpr::None);

    // try to extrac the operation
    let mut split = n.split('-').collect::<Vec<&str>>();

    // if the length is smaller than 4 this is wrong
    if split.len() < 4 {
        panic!("there were too little elements {}", n);
    }

    // it should start with `Op-Iface`
    if split[0] != "Op" || split[1] != "Iface" {
        panic!("Expected operation to start with Op-Iface was {}", n);
    }

    // get the field and slice
    let field = split[2];
    let slice = if split.len() > 4 {
        Some(split[3])
    } else {
        None
    };

    let op = match split.pop() {
        Some("Insert") => Operation::insert(field, slice, arg),
        Some("Extract") => Operation::extract(field, slice),
        Some("WriteAction") => Operation::write(field),
        Some("ReadAction") => Operation::read(field),
        x => panic!("unknown {:?}", x),
    };

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
    Ok((r, vec![Operation::ret()]))
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
    let s = "(Seq (Op-Iface-length-bytes-Insert size) (Seq (Op-Iface-base-address-Insert pa) (Seq (Op-Iface-length-WriteAction) (Seq (Op-Iface-base-WriteAction) (Return)))))\n";
    parse_result(s);

    let s = "(Seq (Op-Iface-length-bytes-Insert (bv #x000000ffffffffff 64)) (Seq (Op-Iface-base-address-Insert (bvlshr pa (bv #x000000000000000c 64))) (Seq (Op-Iface-base-WriteAction) (Seq (Op-Iface-length-WriteAction) (Return)))))\n";
    parse_result(s);
}
