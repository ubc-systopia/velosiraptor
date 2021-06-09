//! Velosiraptor Compiler

// the used nom componets
use nom::{
    bytes::complete::{is_not, tag, take_until},
    sequence::{pair, tuple},
    IResult,
};

// get the tokens
use super::tokens;

/// parses and consumes an end of line comment `// foo`
pub fn comment(input: &str) -> IResult<&str, &str> {
    // Matches a inline comment `//`
    let (input, (_, c)) = pair(tag(tokens::COMMENT), is_not(tokens::EOL))(input)?;
    // return the remainder of the input, and the parsed comment value
    Ok((input.trim(), c.trim()))
}

/// parses and consumes a block comment `/* bar */`
/// TODO: this doesn't work with nested comments!
pub fn blockcomment(input: &str) -> IResult<&str, &str> {
    let (input, (_, c, _)) = tuple((
        // start with the block comment start token
        tag(tokens::COMMENT_BLOCK_START),
        // consume everything until we reach the end of token
        take_until(tokens::COMMENT_BLOCK_END),
        // consume the end token
        tag(tokens::COMMENT_BLOCK_END),
    ))(input)?;
    Ok((input.trim(), c.trim()))
}

#[test]
fn parse_comment_tests() {
    assert_eq!(comment("// foo bar"), Ok(("", "foo bar")));
    assert_eq!(comment("// foo bar\n\n"), Ok(("", "foo bar")));
    assert_eq!(comment("// foo \nbar"), Ok(("bar", "foo")));
}

#[test]
fn parse_blockcomment_tests() {
    assert_eq!(blockcomment("/* foo bar */"), Ok(("", "foo bar")));
    assert_eq!(blockcomment("/* foo \nbar */"), Ok(("", "foo \nbar")));
    assert_eq!(blockcomment("/* foo  */bar"), Ok(("bar", "foo")));
    assert_eq!(blockcomment("/* foo  */\nbar"), Ok(("bar", "foo")));
}
