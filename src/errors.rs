use std::{
    error::Error,
    fmt::{self, Display, Debug, Formatter},
};
use unicode_names2::name;
use crate::text::Span;

pub enum SyntaxError {
    UnexpectedCharacter(Vec<char>, Span),
    UnterminatedString(Span),
    StringInvalidEscSeq(Span),
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use SyntaxError::*;
        f.write_str("Syntax error: ").and_then(|_| match self {
            UnexpectedCharacter(chars, span) => {
                f.write_str(if chars.len() == 1 {
                    if let Some(name) = name(chars[0]) {
                        format!("Unexpected character '{}' at {}", name, span)
                    } else {
                        format!("Unexpected character at {}", span)
                    }
                } else {
                    format!("Unexpected characters at {}", span)
                }.as_str())
            },

            UnterminatedString(span) => {
                f.write_str(format!("The string at {} isn't terminated", span).as_str())
            },

            StringInvalidEscSeq(span) => {
                f.write_str(format!("The string escape sequence at {} is invalid", span).as_str())
            },
        })
    }
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Error for SyntaxError {}
