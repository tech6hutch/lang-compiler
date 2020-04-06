use std::{
    convert::Infallible,
    fmt::{self, Debug, Display, Formatter, Write},
    iter::{Extend, Peekable, once},
};
use bigdecimal::BigDecimal;
use either::Either;
use itertools::Itertools;
use num_bigint::BigInt;
use crate::{
    errors::SyntaxError,
    text::{CharAndPos, EnumerateLineCol, Pos, Span},
    traverser::{ALLOWED_ESCAPE_CHARS, ESCAPE_SEQS},
};

pub fn lex(code: &str) -> Tokens {
    // Parsing can't fail; it stores the errors internally
    code.parse().unwrap()
}

const TOKEN_SYMBOLS: &[char] = &[
    /* conditions */ '=', '<', '>', '?',
    /* arithmetic */ '+', '-', '*', '/',
    /* lists, infix, and expr sep */ ',', '.', ';',
    /* collections (and grouping) */ '(', ')', '[', ']', '{', '}',
];

fn valid_keyword_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}
fn valid_keyword_char(c: char) -> bool {
    c.is_ascii_alphanumeric()
}
fn valid_token_keyword(s: &str) -> bool {
    let mut chars = s.chars();
    chars
        .next()
        .map(|first| valid_keyword_start(first) && chars.all(valid_keyword_char))
        .unwrap_or(false) // "" is not a valid keyword
}

const OPENING_QUOTES: &[char] = &['"'];
const CLOSING_QUOTES: &[char] = &['"'];
// This fn can become const once matching in const fns is stabilized
fn closing_quote(q: char) -> char {
    match q {
        '"' => '"',
        _ => panic!("unknown opening quote")
    }
}

#[derive(Debug)]
pub struct Tokens(Vec<Token>, Vec<SyntaxError>);

impl Tokens {
    pub fn tokens(&self) -> &Vec<Token> {
        &self.0
    }

    pub fn errors(&self) -> &Vec<SyntaxError> {
        &self.1
    }

    pub fn has_errors(&self) -> bool {
        !self.1.is_empty()
    }
}

/// "impl" isn't allowed in type aliases yet, and this type is complex and gross, so
/// I shoved it in a macro.
macro_rules! MyIterType {
    () => {
        &mut Peekable<impl Iterator<Item = CharAndPos>>
    };
}

impl std::str::FromStr for Tokens {
    type Err = Infallible;

    fn from_str(code: &str) -> Result<Self, Self::Err> {
        let mut tokens: Vec<Token> = Vec::new();
        let mut errors: Vec<SyntaxError> = Vec::new();

        let mut iter = code.chars().enumerate_line_col().peekable();
        while let Some((c, pos)) = iter.next() {
            // Remember to update valid_token_start() if you change any of the match cases in this.
            match c {
                | ' '
                | '\t'
                | '\r' => {
                    // Ignore whitespace.
                },

                | '\n'
                | ';' => {
                    tokens.push(Token::Terminator(pos));
                },

                _ if TOKEN_SYMBOLS.contains(&c) => {
                    if c == '.' {
                        // Yes, for numbers we basically parse the decimal part with lookbehind.
                        // Maybe it's dumb, but peeking 2 ahead would be hard with iterators.
                        if let Some(last) = tokens.last_mut() {
                            if let Token::Lit(LiteralToken::Int(int_literal)) = last {
                                match DecimalLiteralToken::try_consume_from(&mut iter, int_literal) {
                                    Ok(token) => *last = Token::Lit(LiteralToken::Dec(token)),
                                    Err(e) => errors.push(e),
                                }
                            }
                        }
                    }
                    tokens.push(Token::Ident(IdentToken::Op(OperatorToken::consume_from(&mut iter, c, pos))))
                },

                _ if valid_keyword_start(c) => {
                    tokens.push(Token::Ident(IdentToken::Kw(KeywordToken::consume_from(&mut iter, c, pos))));
                },

                _ if c.is_ascii_digit() => match IntegerLiteralToken::try_consume_from(&mut iter, c, pos) {
                    Ok(token) => tokens.push(Token::Lit(LiteralToken::Int(token))),
                    Err(e) => errors.push(e),
                },

                _ if OPENING_QUOTES.contains(&c) => match PlainStringToken::try_consume_from(&mut iter, c, pos) {
                    Ok(token) => tokens.push(Token::Lit(LiteralToken::Str(StringLiteralToken::Plain(token)))),
                    Err(e) => errors.push(e),
                },

                _ => {
                    let (chars, span) = collect_while(&mut iter, c, pos, |(c2, _)| !valid_token_start(*c2));
                    errors.push(SyntaxError::UnexpectedCharacter(chars, span));
                },
            }
        }

        Ok(Tokens(tokens, errors))
    }
}

fn valid_token_start(c: char) -> bool {
    match c {
        '\n' | '\r' | '\t' | ' ' => true,

        _ if TOKEN_SYMBOLS.contains(&c) => true,

        _ if valid_keyword_start(c) => true,

        _ if c.is_ascii_digit() => true,

        _ if OPENING_QUOTES.contains(&c) => true,

        _ => false
    }
}

impl From<(Vec<Token>, Vec<SyntaxError>)> for Tokens {
    fn from(tup: (Vec<Token>, Vec<SyntaxError>)) -> Self {
        Self(tup.0, tup.1)
    }
}

/*
Hierarchy:
Token
- TerminatorToken
- IdentToken
  - OperatorToken
  - KeywordToken
- LiteralToken
  - IntegerLiteralToken
  - DecimalLiteralToken (TODO; also I might combine this with IntegerLiteralToken)
  - StringLiteralToken
    - PlainStringToken
    - TemplateStringToken (TODO)
    - RawStringToken/VerbatimStringToken (TODO; maybe can be combined with PlainStringToken)
*/

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Terminator(Pos),
    Ident(IdentToken),
    Lit(LiteralToken),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IdentToken {
    Op(OperatorToken),
    Kw(KeywordToken),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OperatorToken {
    pub kind: OperatorKind,
    pub span: Span,
}
impl OperatorToken {
    fn consume_from(iter: MyIterType!(), start_c: char, start_pos: Pos) -> Self {
        let (lexeme, span) = string_while(iter, start_c, start_pos, |(c, _)| TOKEN_SYMBOLS.contains(c));
        Self {
            kind: OperatorKind::from(lexeme.as_str()),
            span,
        }
    }
}

/// I only list explicit types for operators that require special handling.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OperatorKind {
    ParenOpen,
    ParenClose,
    EmptyParens,
    BracketOpen,
    BracketClose,
    EmptyBrackets,
    BraceOpen,
    BraceClose,
    EmptyBraces,
    Comma,
    Other(String),
}
impl From<&str> for OperatorKind {
    fn from(s: &str) -> Self {
        use OperatorKind::*;
        match s {
            "(" => ParenOpen,
            ")" => ParenClose,
            "()" => EmptyParens,
            "[" => BracketOpen,
            "]" => BracketClose,
            "[]" => EmptyBrackets,
            "{" => BraceOpen,
            "}" => BraceClose,
            "{}" => EmptyBraces,
            "," => Comma,
            _ => Other(s.to_string())
        }
    }
}
impl<'other> From<&'other OperatorKind> for &'other str {
    fn from(op: &'other OperatorKind) -> Self {
        use OperatorKind::*;
        match op {
            ParenOpen => "(",
            ParenClose => ")",
            EmptyParens => "()",
            BracketOpen => "[",
            BracketClose => "]",
            EmptyBrackets => "[]",
            BraceOpen => "{",
            BraceClose => "}",
            EmptyBraces => "{}",
            Comma => ",",
            Other(s) => s.as_str()
        }
    }
}
impl Display for OperatorKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(self.into())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct KeywordToken {
    pub kind: KeywordKind,
    pub span: Span,
}
impl KeywordToken {
    fn consume_from(iter: MyIterType!(), start_c: char, start_pos: Pos) -> Self {
        let (lexeme, span) = string_while(iter, start_c, start_pos, |(c, _)| valid_keyword_char(*c));
        assert!(valid_token_keyword(lexeme.as_str()));
        Self {
            kind: KeywordKind::from(lexeme.as_str()),
            span,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum KeywordKind {
    // Let,
    // Var,
    End,
    Do,
    If,
    Then,
    Else,
    And,
    Or,
    Other(String),
}
impl From<&str> for KeywordKind {
    fn from(s: &str) -> Self {
        use KeywordKind::*;
        match s {
            "end" => End,
            "do" => Do,
            "if" => If,
            "then" => Then,
            "else" => Else,
            "and" => And,
            "or" => Or,
            _ => Other(s.to_string())
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LiteralToken {
    Int(IntegerLiteralToken),
    Dec(DecimalLiteralToken),
    Str(StringLiteralToken),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntegerLiteralToken {
    pub literal: BigInt,
    pub span: Span,
}
impl IntegerLiteralToken {
    fn try_consume_from(iter: MyIterType!(), start_c: char, start_pos: Pos) -> Result<Self, SyntaxError> {
        let (lexeme, span) = try_string_while(iter, Some(start_c), start_pos, digit_not_keyword)?;

        Ok(Self {
            literal: lexeme.parse().expect("this string should be only digits"),
            span,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DecimalLiteralToken {
    pub literal: BigDecimal,
    pub span: Span,
}
impl DecimalLiteralToken {
    fn try_consume_from(iter: MyIterType!(), intLiteral: &IntegerLiteralToken) -> Result<Self, SyntaxError> {
        let start_pos = intLiteral.span.start;
        let (dec_str, span) = try_string_while(iter, None, start_pos, digit_not_keyword)?;

        let big_str: String = format!("{}.{}", intLiteral.literal, dec_str);

        Ok(Self {
            literal: big_str.parse().expect("this string should be valid decimal"),
            span,
        })
    }
}

fn digit_not_keyword((c, pos): &CharAndPos) -> Result<bool, SyntaxError> {
    if c.is_ascii_digit() {
        Ok(true)
    } else if valid_keyword_start(*c) {
        // Operators and whitespace are allowed after a number, but not keywords
        Err(SyntaxError::UnexpectedCharacter(vec![*c], Span::one(*pos)))
    } else {
        // The int is over, stop collecting chars
        Ok(false)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StringLiteralToken {
    Plain(PlainStringToken),
    Template(TemplateStringToken),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PlainStringToken {
    /// Has all the escape sequences replaced.
    pub literal: String,
    pub span: Span,
}
impl PlainStringToken {
    fn try_consume_from(iter: MyIterType!(), start_quote: char, start_pos: Pos) -> Result<Self, SyntaxError> {
        let close_quote = closing_quote(start_quote);
        assert!(CLOSING_QUOTES.contains(&close_quote));
        let mut escaping = false; // whether the prev char was backslash
        let (lexeme, span) = try_string_while(iter, None, start_pos, |(c, pos)| {
            if escaping {
                if *c == '\n' || *c == close_quote || ALLOWED_ESCAPE_CHARS.contains(c) {
                    escaping = false;
                    Ok(true)
                } else {
                    Err(SyntaxError::StringInvalidEscSeq(Span::one(*pos)))
                }
            } else {
                match c {
                    '\n' => {
                        // Strings can't continue across lines unless escaped
                        Err(SyntaxError::UnterminatedString(Span::one(*pos)))
                    },
                    '\\' => {
                        escaping = true;
                        Ok(true)
                    },
                    _ => {
                        // If c is close_quote, the string is over
                        Ok(*c != close_quote)
                    },
                }
            }
        })?;
        
        // We need to consume the closing quote because try_string_while() peeks at chars
        // and only consumes them if the predicate returns Ok(true).
        iter.next();

        let mut escaping = false;
        let mut consuming_leading_whitespace = false;
        let literal = lexeme.chars().filter_map(|c| {
            if consuming_leading_whitespace {
                assert!(!escaping);
                if c == ' ' || c == '\t' {
                    return None; // continue skipping whitespace
                } else {
                    consuming_leading_whitespace = false;
                }
            }

            if escaping {
                escaping = false;
                if c == '\n' {
                    // If c is a literal newline (not backslash n),
                    // then the string continues to the next line.
                    consuming_leading_whitespace = true;
                    None
                } else {
                    assert!(ALLOWED_ESCAPE_CHARS.contains(&c), "but I already checked this");
                    Some(ESCAPE_SEQS[format!("\\{}", c).as_str()].replace)
                }
            } else if c == '\\' {
                escaping = true;
                None
            } else {
                Some(c)
            }
        }).collect();

        Ok(Self {
            literal,
            span,
        })
    }
}

pub type StringTemplate = Vec<Either<PlainStringToken, KeywordToken>>;
// TODO: implement this string type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TemplateStringToken {
    pub template: StringTemplate,
    pub span: Span,
}

// Iterator consumption helper methods

/// Take a string from `iter` while `accept` returns `true`.
///
/// * `start_c`: A `char` to start the string with.
/// * `start_pos`: A `Pos` to make the `Span` with.
fn string_while(
    iter: MyIterType!(),
    start_c: char,
    start_pos: Pos,
    accept: impl FnMut(&CharAndPos) -> bool,
) -> (String, Span) {
    collect_while(iter, start_c, start_pos, accept)
}

/// Take a collection from `iter` while `accept` returns `true`.
///
/// * `start_c`: A `char` to start the collection with.
/// * `start_pos`: A `Pos` to make the `Span` with.
fn collect_while<Coll>(
    iter: MyIterType!(),
    start_c: char,
    start_pos: Pos,
    accept: impl FnMut(&CharAndPos) -> bool,
) -> (Coll, Span)
where
    Coll: Default + Extend<char>,
{
    let (lexeme, positions): (Coll, Vec<Pos>) = once((start_c, start_pos))
        .chain(iter.peeking_take_while(accept))
        .unzip();

    (
        lexeme,
        Span {
            start: start_pos,
            end: *positions.last().expect("this can't be empty because I created it with an element"),
        },
    )
}

/// Take a string from `iter` while `accept` returns `Ok(true)`. Stops on `Ok(false)` or `Err(_)`.
///
/// * `start_c`: A `char` to start the string with, if provided.
/// * `start_pos`: A `Pos` to make the `Span` with.
fn try_string_while(
    iter: MyIterType!(),
    start_c: Option<char>,
    start_pos: Pos,
    mut accept: impl FnMut(&CharAndPos) -> Result<bool, SyntaxError>,
) -> Result<(String, Span), SyntaxError> {
    let mut lexeme = start_c.map(|c| c.to_string()).unwrap_or_default();
    let mut end_pos = start_pos;

    while let Some(char_and_pos) = iter.peek() {
        if !accept(char_and_pos)? {
            break;
        }

        lexeme.push(char_and_pos.0);
        end_pos = char_and_pos.1;
        iter.next(); // don't want an infinite loop
    }

    Ok((
        lexeme,
        Span { start: start_pos, end: end_pos },
    ))
}
