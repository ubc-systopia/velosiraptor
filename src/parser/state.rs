// Velosiraptor Compiler
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

// the used nom componets
use nom::{
    bytes::complete::tag,
    character::complete::{digit1, multispace0, multispace1},
    multi::separated_list1,
    sequence::{delimited, preceded, terminated, tuple},
    IResult,
};

// get the tokens
use super::comments::parse_comments;
use super::identifier::parse_identifier;
use super::tokens::{comma, lbrace, lbrack, rbrace, rbrack, semicolon};
use super::SourcePos;

use super::ast::{StateField, BitMapEntry};



fn parse_field_entry(input: SourcePos) -> IResult<SourcePos, BitMapEntry> {
    // an entry is basically two numbers followed by an identifier
    let mut p = tuple((
        // we start with a digit
        digit1,
        // then we have at lest one white space, followed by another digit
        preceded(multispace1, digit1),
        // then we have at lest one whitespace, followd by an identifyer, and maybe some whitespace
        delimited(multispace1, parse_identifier, multispace0),
    ));

    let pos = input.get_pos();

    let (input, start, end, identifier) = match p(input) {
        Ok((input, (start, end, identifier))) => (
            input,
            start.as_slice().parse::<u16>().unwrap(),
            end.as_slice().parse::<u16>().unwrap(),
            identifier,
        ),
        Err(x) => {
            println!("parsing error: number expected.");
            println!("{}", input);
            return Err(x);
        }
    };

    Ok((input, BitMapEntry::new(start, end, identifier, pos)))
}

fn parse_field(input: SourcePos) -> IResult<SourcePos, StateField> {
    // get the current position
    let pos = input.get_pos();

    // the field location is `IDENTIFIER, 0, 4`
    let field_location = tuple((
        // identifier ending in a comma
        terminated(parse_identifier, comma),
        // digit ending in a comment
        terminated(digit1, comma),
        // finally a digit
        digit1,
    ));

    // the entries are a comma separeted list entries, where each entry may have some comments before
    let field_entries = separated_list1(comma, preceded(parse_comments, parse_field_entry));

    // a field has the form //  IDENTIFIER [ IDENTIFIER, 0, 4 ] { <ENTRIES> };
    let mut field = terminated(
        tuple((
            // we start with an identifier, followed by maybe whitespace
            parse_identifier,
            // then we have a `[` FIELD_LOCATION `]`
            delimited(lbrack, field_location, rbrack),
            // then we have a `{` FIELD_ENTRIES `}`
            delimited(lbrace, field_entries, rbrace),
        )),
        tuple((parse_comments, semicolon)),
    );

    let (input, name, base, offset, length, bitmap) = match field(input) {
        Ok((input, (name, (base, offset, length), bitmap))) => (
            input,
            name,
            base,
            offset.as_slice().parse::<u64>().unwrap(),
            length.as_slice().parse::<u64>().unwrap(),
            bitmap,
        ),
        Err(x) => {
            println!("parsing error: unclosed block comment");
            println!("{}", input);
            return Err(x);
        }
    };

    //  pte [base, 0, 4] { <ENTRIES> };

    Ok((
        input,
        StateField::new(name, base, offset, length, bitmap, pos),
    ))
}

// /// parses and consumes an import statement (`import foo;`) and any following whitespaces
// pub fn parse_state(input: SourcePos) -> IResult<SourcePos, Import> {
//     // record the current position
//     let pos = input.get_pos();

// }

#[test]
fn parse_field_entry_test() {
    assert_eq!(
        parse_field_entry(SourcePos::new("stdin", "0 12 foo")),
        Ok((
            SourcePos::new_at("stdin", "", 8, 1, 9),
            BitMapEntry {
                start: 0,
                end: 12,
                name: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
    assert_eq!(
        parse_field_entry(SourcePos::new("stdin", "13\n 12\t foo")),
        Ok((
            SourcePos::new_at("stdin", "", 11, 2, 9),
            BitMapEntry {
                start: 13,
                end: 12,
                name: "foo".to_string(),
                pos: (1, 1)
            }
        ))
    );
}

#[test]
fn parse_field_test() {
    assert_eq!(
        parse_field(SourcePos::new("stdin", "foo [ bar, 0, 2 ] { 1 2 foobar };")),
        Ok((
            SourcePos::new_at("stdin", "", 33, 1, 34),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (1, 21)
                }],
                pos: (1, 1)
            },
        ))
    );

    assert_eq!(
        parse_field(SourcePos::new("stdin", "foo[bar,0,2] {1 2 foobar};")),
        Ok((
            SourcePos::new_at("stdin", "", 26, 1, 27),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (1, 15)
                }],
                pos: (1, 1)
            },
        ))
    );

    assert_eq!(
        parse_field(SourcePos::new("stdin", "foo[bar,0,2] {// some comment \n 1 2 foobar\n};")),
        Ok((
            SourcePos::new_at("stdin", "", 45, 3, 3),
            StateField {
                name: "foo".to_string(),
                base: "bar".to_string(),
                offset: 0,
                length: 2,
                bitmap: vec![BitMapEntry {
                    start: 1,
                    end: 2,
                    name: "foobar".to_string(),
                    pos: (2, 2)
                }],
                pos: (1, 1)
            },
        ))
    );
}
