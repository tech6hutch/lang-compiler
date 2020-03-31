use std::fmt::{self, Display, Debug, Formatter};
use std::error::Error;
use crate::text::Span;

#[derive(Debug)]
pub enum SyntaxError {
    UnexpectedCharacter(Vec<char>, Span),
    UnterminatedString(Span),
    StringInvalidEscSeq(Span),
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        todo!();
    }
}

impl Error for SyntaxError {}
