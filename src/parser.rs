use std::{
    fmt::{self, Display, Debug, Formatter},
    iter::Peekable,
};
use bigdecimal::BigDecimal;
use if_chain::if_chain;
use num_bigint::BigInt;
use crate::{
    errors::SyntaxError,
    lexer::{
        self,
        Token, Tokens,
        OperatorToken, OperatorKind,
    },
};

pub fn print_ast(expr: &Expression) -> String {
    return match expr {
        Expression::Grouping(expr) => parenthesize("group", &[expr]),
        Expression::Binary(expr) => parenthesize(&expr.operator.kind, &[expr.left.as_ref(), expr.right.as_ref()]),
        Expression::Unary(expr) => parenthesize(&expr.operator.kind, &[expr.right.as_ref()]),
        Expression::Int(IntegerLiteral { value }) => value.to_string(),
        Expression::Dec(DecimalLiteral { value }) => value.to_string(),
        Expression::Str(StringLiteral { value }) => value.clone(),
    };

    fn parenthesize<'a, T: Into<&'a str>>(name: T, exprs: &[&Expression]) -> String {
        let mut s = ["(", name.into()].concat();
        for expr in exprs {
            let expr_s = print_ast(expr);
            s.reserve(expr_s.len() + 1);
            s.push(' ');
            s += &expr_s;
        }
        s.push(')');
        s
    }
}

pub fn parse(tokens: &Tokens) -> Result<Expression, Vec<SyntaxError>> {
    // TODO: Maybe try to parse anyway, to catch later errors.
    if tokens.has_errors() {
        return Err(tokens.errors().to_owned());
    }

    let mut iter = tokens.tokens().iter().cloned().peekable();
    expression(&mut iter)
        .map_err(|e| vec![e])
}

/*
Operator precedence:
expression     = comparison ;
comparison     = addition ( ( "<" | "<=" | "=?" | ">" | ">=" ) )* ;
addition       = multiplication ( ( "-" | "+" ) )* ;
multiplication = unary ( ( "/" | "*" ) unary )* ;
unary          = ( "-" ) unary
               | primary ;
primary        = NUMBER | STRING
               | "(" expression ")" ;
*/

/// "impl" isn't allowed in type aliases yet, and this type is complex and gross, so
/// I shoved it in a macro.
macro_rules! MyIterType {
    () => {
        &mut Peekable<impl Iterator<Item = Token>>
    };
    ($Iterator:ty) => {
        &mut Peekable<$Iterator>
    };
}

fn expression(iter: MyIterType!()) -> ExprResult {
    comparison(iter)
}

fn match_op_str(iter: MyIterType!(), ops: &[&'static str]) -> Option<OperatorToken> {
    if_chain! {
        if let Some(Token::OpIdent(op_token)) = iter.peek();
        if let OperatorToken { kind: OperatorKind::Other(s), .. } = op_token;
        if ops.contains(&s.as_str());
        then {
            Some(op_token.clone())
        } else {
            None
        }
    }
}

fn match_op(iter: MyIterType!(), op: OperatorKind) -> Option<OperatorToken> {
    if_chain! {
        if let Some(Token::OpIdent(op_token)) = iter.peek();
        if op_token.kind == op;
        then {
            Some(op_token.clone())
        } else {
            None
        }
    }
}

type ExprResult = Result<Expression, SyntaxError>;

fn binary<I, F>(
    iter: MyIterType!(I),
    ops_to_match: &[&'static str],
    next_higher_precedence: F,
) -> ExprResult
where
    I: Iterator<Item = Token>,
    F: Fn(MyIterType!(I)) -> ExprResult,
{
    let mut expr: Expression = next_higher_precedence(iter)?;

    while let Some(op) = match_op_str(iter, ops_to_match) {
        iter.next();
        let right: Expression = next_higher_precedence(iter)?;
        expr = Expression::Binary(BinaryExpr::new(expr, op, right));
    }

    return Ok(expr);
}

fn comparison(iter: MyIterType!()) -> ExprResult {
    binary(iter, &["<", "<=", "=?", ">", ">="], addition)
}

fn addition(iter: MyIterType!()) -> ExprResult {
    binary(iter, &["-", "+"], multiplication)
}

fn multiplication(iter: MyIterType!()) -> ExprResult {
    binary(iter, &["/", "*"], unary)
}

fn unary(iter: MyIterType!()) -> ExprResult {
    if let Some(op) = match_op_str(iter, &["-"]) {
        iter.next();
        let right: Expression = unary(iter)?;
        Ok(Expression::Unary(UnaryExpr::new(op, right)))
    } else {
        primary(iter)
    }
}

fn primary(iter: MyIterType!()) -> ExprResult {
    Ok(match iter.next() {
        Some(Token::Int(int_token)) => {
            Expression::Int(IntegerLiteral { value: int_token.literal.clone() })
        }
        Some(Token::Dec(dec_token)) => {
            Expression::Dec(DecimalLiteral { value: dec_token.literal.clone() })
        }
        Some(Token::Str(str_token)) => {
            Expression::Str(StringLiteral { value: str_token.literal.clone() })
        }

        Some(Token::OpIdent(OperatorToken { kind: OperatorKind::ParenOpen, .. })) => {
            let expr: Expression = expression(iter)?;
            consume_op(iter, OperatorKind::ParenClose, "Expect ')' after expression.")?;
            Expression::Grouping(Box::new(expr))
        }

        maybe_token => return Err(SyntaxError::ExpectedExpr(maybe_token))
    })
}

fn consume_op(iter: MyIterType!(), op: OperatorKind, error_msg: &'static str) -> Result<Token, SyntaxError> {
    if match_op(iter, op).is_some() {
        Ok(iter.next().unwrap())
    } else {
        Err(iter.peek().cloned()
            .map(|token| SyntaxError::UnexpectedToken(token, Some(error_msg)))
            .unwrap_or_else(|| SyntaxError::UnexpectedEndOfFile(Some(error_msg))))
    }
}

fn synchronize(iter: MyIterType!()) {
    while let Some(token) = iter.next() {
        if let Token::Terminator(..) = token {
            return;
        }

        if let Some(Token::KwIdent(keyword)) = iter.peek() {
            use lexer::KeywordKind;
            match keyword.kind {
                KeywordKind::If => return,
                _ => {}
            }
        }
    }
}

/*
Hierarchy:
Expression
// IdentExpr
- OperatorExpr
- KeywordExpr
// LiteralExpr
- IntegerLiteral
// StringLiterals
- PlainStringLiteral
- TemplateLiteral
// CollectionLiterals
- ListLiteral
- TupleLiteral
- RecordLiteral
- InvocationExpr
*/

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression {
    // Identifiers (TODO: reorganize)
    // Ident(IdentExpr)

    // Literals
    Int(IntegerLiteral),
    Dec(DecimalLiteral),
    Str(StringLiteral),
    // Temp(TemplateStringLiteral), TODO

    // Invocations and nesting
    // Invoke(InvocationExpr),
    Grouping(Box<Expression>),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnaryExpr {
    pub operator: OperatorToken,
    pub right: Box<Expression>,
}
impl UnaryExpr {
    fn new(operator: OperatorToken, right: Expression) -> Self {
        Self {
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BinaryExpr {
    pub left: Box<Expression>,
    pub operator: OperatorToken,
    pub right: Box<Expression>,
}
impl BinaryExpr {
    fn new(left: Expression, operator: OperatorToken, right: Expression) -> Self {
        Self {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        }
    }
}

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum IdentExpr {
//     Op(OperatorExpr),
//     Kw(KeywordExpr),
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct OperatorExpr { name: String }
// #[derive(Debug, PartialEq, Eq, Clone, Hash)]
// pub struct KeywordExpr { name: String }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum LiteralExpr {
//     Int(IntegerLiteral),
//     Str(StringLiteral),
//     // Coll(CollectionLiteral),
// }

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntegerLiteral { pub value: BigInt }

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DecimalLiteral { pub value: BigDecimal }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum StringLiteral {
//     Plain(PlainStringLiteral),
//     // Template(TemplateLiteral),
// }

#[derive(Debug, PartialEq, Eq, Clone)]
// pub struct PlainStringLiteral { pub value: String }
pub struct StringLiteral { pub value: String }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct TemplateStringLiteral { value: Vec<Either<String, KeywordExpr>> }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum CollectionLiteral {
//     List(ListLiteral),
//     Tup(TupleLiteral),
//     Rec(RecordLiteral),
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct ListLiteral {
//     value: Vec<Expression>,
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct TupleLiteral {
//     value: Vec<(KeywordExpr, Expression)>,
// }
// impl TupleLiteral {
//     fn unit() -> Self {
//         Self { value: Vec::default() }
//     }
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct RecordLiteral {
//     value: HashMap<KeywordExpr, Expression>,
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum InvocationExpr {
//     Un(UnaryExpr),
//     Bin(BinaryExpr),
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct UnaryExpr {
//     callee: KeywordExpr,
// }

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct BinaryExpr {
//     callee: KeywordExpr,
//     arg: Box<Expression>,
// }

// TODO

// pub struct OperatorChain(Expression, OperatorChainTail);

// pub struct OperatorChainTail(OperatorExpr, Expression, Option<Box<OperatorChainTail>>);

/*
TODO: move description somewhere more appropriate.
Operator hierarchy (from closest binding to furthest):
Collection literals: ( ) [ ] { } ,
Infix: .
Multiplication: * /
Addition: + -
Comparison: =? < > <= >=
*/

// pub struct OperatorDefinition {
//     name: String,
//     category: DefinedOperatorCategory,
//     position_in_category: PositionInCategory,
// }

// pub enum DefinedOperatorCategory {
//     // No precedence (requires parentheses)
//     Uncategorized,
//     // Binary
//     Comparison,
//     Arithmetic,
//     // Unary
//     Unary,
// }

// pub enum PositionInCategory {
//     YieldsToOthersInCategory,
//     BindsCloserThanOthersInCategory,
// }

// pub fn parse(tokens: Tokens) -> Result<SyntaxTree, SyntaxError> {
//     let root_body = tokens.into_inner().into_iter()
//         .batching(parse_expression)
//         .collect::<Result<Vec<_>, SyntaxError>>()?;

//     let root = BlockExpr { body: root_body };
//     Ok(SyntaxTree { root })
// }

// const EXPR_TERMINATORS: &[char] = &['\n'];

// /// Returns:
// /// - None if there are no more tokens
// /// - Some(Ok) if successfully parsed token(s)
// /// - Some(Err) if parsing failed on any token in this expression (or its children)
// fn parse_expression(it: &mut impl Iterator<Item = Token>) -> Option<Result<Expression, SyntaxError>> {
//     it.find_map(|token| Some(match token.kind {
//         TokenKind::Whitespace => Ok(if_some(EXPR_TERMINATORS.contains(&token.whitespace_char().unwrap()),
//             Expression::ExprTerminator)?),

//         TokenKind::UnknownWhitespace => Err(SyntaxError::UnknownWhitespace(token.value, token.span)),

//         TokenKind::OperatorIdent => match token.whitespace_char() {
//             None => Ok(Expression::Op(Operator::from(token.value))),

//             // TODO
//             Some(_) => unimplemented!(),
//         //     Some('[') => {
//         //         const comma: TokenKind = TokenKind::MagicOperatorIdent(lexer::MagicOperator::Comma);
//         //         let nested = 0;
//         //         let result = it.take_while(|token| match token.whitespace_char() {
//         //             None => true,
//         //             Some(']') => if nested > 0 {
//         //                 nested -= 1;
//         //                 true
//         //             } else {
//         //                 false
//         //             },
//         //             Some('[') => {
//         //                 nested += 1;
//         //                 true
//         //             },
//         //             Some(_) => true
//         //         }).batching(|it| Some(it
//         //             .take_while(|token| !(nested == 0 && token.kind == comma))))
//         //         .map(|it2| it2.batching(parse_expression).collect::<Vec<Result<Expression, SyntaxError>>>())
//         //         // TODO: maybe have InnerError<Vec<SyntaxError>>
//         //         .collect::<Result<Expression, SyntaxError>>();
//         //         result?
//         //     },
//         },

//         TokenKind::MagicOperatorIdent(..) => unimplemented!(), // TODO

//         TokenKind::UnknownSymbol => Err(SyntaxError::UnknownSymbol(token.value, token.span)),

//         TokenKind::KeywordIdent => Ok(Expression::Keyword(Keyword::from(token.value))),

//         TokenKind::Integer => Ok(Expression::IntLiteral(token.value)),

//         TokenKind::String => StringExpr::try_from(token).map(Expression::String).map_err(Into::into),

//         TokenKind::Unknown => Err(SyntaxError::Other(token.span)),
//     }))
// }

// pub enum SyntaxError {
//     UnknownWhitespace(String, Span),
//     UnknownSymbol(String, Span),
//     String(StringSyntaxError),
//     Other(Span),
//     InnerError { name: String, inner: Box<SyntaxError> },
// }

// impl SyntaxError {
//     fn msg(&self) -> String {
//         use SyntaxError::*;
//         format!("Syntax error: {}", match self {
//             UnknownWhitespace(s, span) => format!("Weird whitespace character {name}at {span}",
//                 span=span, name=format_first_char_name(s)),
//             UnknownSymbol(s, span) => format!("Unknown symbol '{}' at {}", s, span),
//             String(inner) => inner.to_string(),
//             Other(span) => format!("Wtf is that at {}???", span),
//             InnerError { name, inner } => format!("In {}: {}", name, inner.msg()),
//         })
//     }

//     fn get_innermost(&self) -> &Self {
//         let mut e = self;
//         while let SyntaxError::InnerError { inner, .. } = e {
//             e = inner;
//         }
//         e
//     }

//     fn has_inner(&self) -> bool {
//         if let SyntaxError::InnerError { .. } = self {
//             true
//         } else {
//             false
//         }
//     }
// }

// impl Display for SyntaxError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         f.write_str(&self.msg())
//     }
// }

// impl Debug for SyntaxError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         Display::fmt(self, f)
//     }
// }

// impl Error for SyntaxError {
//     fn source(&self) -> Option<&(dyn Error + 'static)> {
//         if self.has_inner() {
//             Some(self.get_innermost())
//         } else {
//             None
//         }
//     }
// }

// impl From<StringSyntaxError> for SyntaxError {
//     fn from(e: StringSyntaxError) -> Self {
//         SyntaxError::String(e)
//     }
// }

// pub struct SyntaxTree {
//     root: BlockExpr,
// }

// // TODO: group the literals under an Expression::Literal?
// pub enum Expression {
//     ExprTerminator,
//     IntLiteral(String),
//     String(StringExpr),
//     List(ListLiteral),
//     Tup(TupleLiteral),
//     Rec(RecordLiteral),
//     Op(Operator),
//     Keyword(Keyword),
//     Block(BlockExpr),
// }

// impl Expression {
//     pub fn unit() -> Expression {
//         Expression::Tup(TupleLiteral(Vec::default()))
//     }

//     pub fn is_ident(&self) -> bool {
//         match self {
//             Expression::Op(..) | Expression::Keyword(..) => true,
//             _ => false
//         }
//     }
// }

// pub enum StringExpr {
//     Literal(String),
//     Template(Vec<Either<String, Keyword>>),
//     Verbatim(String),
// }

// impl TryFrom<Token> for StringExpr {
//     type Error = StringSyntaxError;
//     fn try_from(token: Token) -> Result<Self, Self::Error> {
//         let s = token.value;
//         assert!(!s.is_empty());
//         assert!(s.starts_with('"'));

//         if !s.ends_with('"') {
//             let mut pos = token.span.end;
//             pos.col += 1;
//             return Err(StringSyntaxError::UnescapedNewline(pos));
//         }

//         let escape_seqs = s.chars().enumerate_line_col().batching(|it| it
//             .find_map(|(c, pos)| if_some(c == '\\', pos))
//             .map(|pos| (
//                 pos,
//                 it.next().map(|(c, _)| c),
//             )));
//         for (backslash_pos, esc_char) in escape_seqs {
//             let start = token.span.start + backslash_pos;
//             let end;
//             if let Some(esc_char) = esc_char {
//                 if !ALLOWED_ESCAPE_CHARS.contains(&esc_char) {
//                     end = start.next_col();
//                 } else {
//                     continue;
//                 }
//             } else {
//                 // There was no char after the backslash!
//                 end = start;
//             }
//             return Err(StringSyntaxError::InvalidEscapeSeq(Span { start, end }));
//         }

//         // TODO: template and verbatim string conversion
//         Ok(StringExpr::Literal(s))
//     }
// }

// pub enum StringSyntaxError {
//     UnescapedNewline(Pos),
//     InvalidEscapeSeq(Span),
// }

// impl Display for StringSyntaxError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         use StringSyntaxError::*;
//         f.write_str(match self {
//             UnescapedNewline(pos) => format!(
//                 "Invalid newline at {}.\n\n\
//                 Strings cannot span more than one line unless you escape them with a backslash. Perhaps you forgot to close the string?",
//                 pos
//             ),
//             InvalidEscapeSeq(span) => format!(
//                 "Invalid escape sequence at {}. Allowed are {}.",
//                 span, ESCAPE_SEQS.iter().map(|(seq, EscSeq { desc, .. })| format!("{} ({})", seq, desc)).join(", ")
//             ),
//         }.as_str())
//     }
// }

// impl Debug for StringSyntaxError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         Display::fmt(self, f)
//     }
// }

// impl Error for StringSyntaxError {}

// pub struct ListLiteral(Vec<Expression>);

// pub struct TupleLiteral(Vec<(String, Expression)>);

// pub struct RecordLiteral(HashMap<String, Expression>);

// pub enum CollectionSyntaxError {
//     NoClosingToken {
//         kind: CollectionType,
//         coll_span: Span,
//         first_line_end: Pos,
//     },
// }

// impl Display for CollectionSyntaxError {
//     fn fmt(&self, f: &mut Formatter) -> fmt::Result {
//         use CollectionSyntaxError::*;
//         f.write_str(match self {
//             &NoClosingToken { kind, coll_span, first_line_end } => {
//                 let mut msg = format!(
//                     "No closing '{close_token}' found for the {kind} at {coll_span}",
//                     close_token=kind.close_token(), kind=kind.name(), coll_span=coll_span,
//                 );
//                 if coll_span.end != first_line_end {
//                     msg += format!(
//                         "\nPerhaps you forgot to put it at the end of line {}?",
//                         first_line_end.line
//                     ).as_str();
//                 }
//                 msg
//             },
//         }.as_str())
//     }
// }

// #[derive(Copy, Clone, PartialEq, Eq)]
// pub enum CollectionType { List, Tuple, Record }

// impl CollectionType {
//     pub fn name(&self) -> &'static str {
//         use CollectionType::*;
//         match self {
//             List => "list",
//             Tuple => "tuple",
//             Record => "record",
//         }
//     }

//     pub fn close_token(&self) -> &'static str {
//         use CollectionType::*;
//         match self {
//             List => "]",
//             Tuple => ")",
//             Record => "}",
//         }
//     }
// }

// pub enum Operator {
//     // ParenOpen,
//     // ParenClose,
//     // BracketOpen,
//     // BracketClose,
//     // BraceOpen,
//     // BraceClose,
//     Other(String),
// }

// impl From<String> for Operator {
//     fn from(s: String) -> Self {
//         use Operator::*;
//         match s.as_str() {
//             // "(" => ParenOpen,
//             // ")" => ParenClose,
//             // "[" => BracketOpen,
//             // "]" => BracketClose,
//             // "{" => BraceOpen,
//             // "}" => BraceClose,
//             _ => Other(s)
//         }
//     }
// }

// pub enum Keyword {
//     Other(String),
// }

// impl From<String> for Keyword {
//     fn from(s: String) -> Self {
//         Keyword::Other(s)
//     }
// }

// pub struct BlockExpr {
//     body: Vec<Expression>,
// }
