use std::{
    error::Error,
    fmt::{self, Display, Debug, Formatter},
};
use itertools::Itertools;
use unicode_names2::name;
use crate::{
    lexer::Token,
    text::Span,
    util::{if_and_then, s_if_plural, space_quote_nonempty},
};

#[derive(Clone)]
pub enum SyntaxError {
    UnexpectedCharacter(Vec<char>, Span),
    UnterminatedString(Span),
    StringInvalidEscSeq(Span),
    UnexpectedEndOfFile(Option<&'static str>),
    UnexpectedToken(Token, Option<&'static str>),
    ExpectedExpr(Option<Token>),
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("Syntax error: ")?;

        use SyntaxError::*;
        match self {
            UnexpectedCharacter(chars, span) => {
                // all_equal() defaults to true when len <= 1
                let c_name_or_empty: String = if_and_then(chars.iter().all_equal(), || name(chars[0]))
                    .map(|c_name| c_name.to_string())
                    .unwrap_or_default();
                write!(f, "Unexpected{} character{} at {}",
                    space_quote_nonempty(c_name_or_empty), s_if_plural(chars), span)
            },

            UnterminatedString(span) => {
                write!(f, "The string at {} isn't terminated", span)
            },

            StringInvalidEscSeq(span) => {
                write!(f, "The string escape sequence at {} is invalid", span)
            },

            UnexpectedEndOfFile(msg) => {
                f.write_str("Unexpectedly reached the end of the file")?;
                if let Some(msg) = msg {
                    write!(f, ". {}", msg)?;
                }
                Ok(())
            },

            UnexpectedToken(token, msg) => {
                write!(f, "Unexpected token at {}", token.span())?;
                if let Some(msg) = msg {
                    write!(f, ". {}", msg)?;
                }
                Ok(())
            },

            ExpectedExpr(Some(token)) => {
                write!(f, "Expected expression at {}", token.span())
            },
            ExpectedExpr(None) => {
                f.write_str("Expected expression")
            }
        }
    }
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Error for SyntaxError {}
