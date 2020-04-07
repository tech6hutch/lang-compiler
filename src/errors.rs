use std::iter::once;
use std::{
    error::Error,
    fmt::{self, Display, Debug, Formatter},
};
use itertools::Itertools;
use unicode_names2::name;
use crate::{
    lexer::Token,
    text::Span,
    util::if_and_then,
};

#[derive(Clone)]
pub enum SyntaxError {
    UnexpectedCharacter(Vec<char>, Span),
    UnterminatedString(Span),
    StringInvalidEscSeq(Span),
    UnexpectedEndOfFile,
    UnexpectedToken(Token),
    ExpectedExpr(Option<Token>),
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use SyntaxError::*;
        f.write_str("Syntax error: ").and_then(|_| match self {
            UnexpectedCharacter(chars, span) => {
                assert!([1, 1, 1].iter().all_equal());
                assert!([1, 1].iter().all_equal());
                assert!([1].iter().all_equal());

                // all_equal() returns true when len = 1
                let c_name: String = if_and_then(chars.iter().all_equal(), || name(chars[0]))
                        .map(|c_name| once("'").chain(c_name).chain(once("' ")).collect())
                        .unwrap_or_default();
                f.write_str(format!("Unexpected {}character{} at {}",
                    c_name, if chars.len() == 1 { "" } else { "s" }, span).as_str())
            },

            UnterminatedString(span) => {
                f.write_str(format!("The string at {} isn't terminated", span).as_str())
            },

            StringInvalidEscSeq(span) => {
                f.write_str(format!("The string escape sequence at {} is invalid", span).as_str())
            },

            UnexpectedEndOfFile => {
                f.write_str("Unexpectedly reached the end of the file")
            },

            UnexpectedToken(token) => {
                f.write_str(format!("Unexpected token at {}", token.span()).as_str())
            },

            ExpectedExpr(Some(token)) => {
                f.write_str(format!("Expected expression at {}", token.span()).as_str())
            },
            ExpectedExpr(None) => {
                f.write_str("Expected expression")
            }
        })
    }
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Error for SyntaxError {}
