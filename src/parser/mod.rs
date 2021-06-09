//! Velosiraptor Compiler

// for reading the file
use std::fs;

// the used nom componets
use nom::{
    branch::alt,
    bytes::complete::{is_a, is_not, tag, take_until},
    character::complete::multispace0,
    error::ParseError,
    multi::many0,
    sequence::{delimited, pair, tuple},
    IResult,
};

fn comment(input: &str) -> IResult<&str, &str> {
    // Matches a inline comment `//`
    let (input, _) = pair(tag("//"), is_not("\n"))(input)?;
    Ok((input, "asdf"))
}

fn blockcomment(input: &str) -> IResult<&str, &str> {
    let (input, _) = tuple((tag("/*"), take_until("*/"), tag("*/")))(input)?;
    Ok((input, "asdf"))
}

fn whitespace(input: &str) -> IResult<&str, &str> {
    let (input, _) = is_a(" \t\n\r")(input)?;
    Ok((input, "asdf"))
}

fn skip_white_space_and_comments(input: &str) -> IResult<&str, &str> {
    // can be zero or one
    let (input, _) = many0(alt((comment, whitespace, blockcomment)))(input)?;
    Ok((input, "asdf"))
}

fn parse_unit(input: &str) -> IResult<&str, &str> {
    let (input, _) = ws(tag("unit"))(input)?;
    let (input, _) = ws(tag("{"))(input)?;
    let (input, _) = ws(tag("}"))(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, "asdf"))
}

//fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(
    inner: F,
) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(multispace0, inner, multispace0)
}

fn parse(input: &str) -> IResult<&str, &str> {
    println!("<parsing>");
    println!("{}", input);
    println!("</parsing>");

    let (input, _) = skip_white_space_and_comments(input)?;
    println!("<parsing>");
    println!("{}", input);
    println!("</parsing>");

    let (input, _) = many0(parse_unit)(input)?;
    println!("<parsing>");
    println!("{}", input);
    println!("</parsing>");

    let (input, _) = skip_white_space_and_comments(input)?;
    println!("<parsing>");
    println!("{}", input);
    println!("</parsing>");

    Ok(("asdf", "asdf"))
}

pub fn parse_file(filename: &str) -> IResult<&str, &str> {
    let contents = fs::read_to_string(filename).expect("Something went wrong reading the file");
    let _ret = parse(&contents);
    return Ok(("asdf", "asdf"));
}
