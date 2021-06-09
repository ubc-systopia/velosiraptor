//! specifies special parsing tokens for velosiraptor.

/// represents the end of line string.
pub const EOL: &str = "\n";

/// represents the start of a end of line comment
pub const COMMENT: &str = "//";

/// represents the start of a block comment
pub const COMMENT_BLOCK_START: &str = "/*";

/// represents the end of a block comment
pub const COMMENT_BLOCK_END: &str = "*/";
