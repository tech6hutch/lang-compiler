use std::fmt::{self, Display, Formatter};
use bigdecimal::BigDecimal;
use num_bigint::BigInt;
use crate::{
    errors::RuntimeError,
    parser::{Expression, /*IntegerLiteral, DecimalLiteral, StringLiteral, UnaryExpr, BinaryExpr*/},
};

pub enum RuntimeValue {
    Int(BigInt),
    Dec(BigDecimal),
    Str(String),
}

impl From<BigInt> for RuntimeValue {
    fn from(x: BigInt) -> Self { RuntimeValue::Int(x) }
}
impl From<BigDecimal> for RuntimeValue {
    fn from(x: BigDecimal) -> Self { RuntimeValue::Dec(x) }
}
impl From<String> for RuntimeValue {
    fn from(x: String) -> Self { RuntimeValue::Str(x) }
}

impl Display for RuntimeValue {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            RuntimeValue::Int(x) => write!(f, "{}", x),
            RuntimeValue::Dec(x) => write!(f, "{}", x),
            RuntimeValue::Str(x) => write!(f, "{}", x),
        }
    }
}

pub fn interpret(expr: &Expression) -> Result<RuntimeValue, RuntimeError> {
    evaluate(expr)
}

fn evaluate(expr: &Expression) -> Result<RuntimeValue, RuntimeError> {
    use Expression as Expr;
    use crate::lexer::OperatorKind;
    Ok(match expr {
        Expr::Int(e) => e.value.clone().into(),
        Expr::Dec(e) => e.value.clone().into(),
        Expr::Str(e) => e.value.clone().into(),

        Expr::Grouping(boxed) => evaluate(boxed)?,

        Expr::Unary(e) => {
            let right = evaluate(&e.right)?;
            if let OperatorKind::Other(ref s) = e.operator.kind {
                match s.as_str() {
                    "-" => match right {
                        RuntimeValue::Int(rhs) => RuntimeValue::Int(-rhs),
                        RuntimeValue::Dec(rhs) => RuntimeValue::Dec(-rhs),
                        RuntimeValue::Str(_) => return Err(RuntimeError::OperandTypeError {
                            arity: 1,
                            operator: e.operator.clone(),
                            type_str: "a number",
                        }),
                    },
                    _ => todo!("give error")
                }
            } else {
                unreachable!("I think?");
            }
        },

        Expr::Binary(e) => {
            let left = evaluate(&e.left)?;
            let right = evaluate(&e.right)?;
            if let OperatorKind::Other(ref s) = e.operator.kind {
                match s.as_str() {
                    "-" => match left {
                        RuntimeValue::Int(lhs) => match right {
                            RuntimeValue::Int(rhs) => RuntimeValue::Int(lhs - rhs),
                            _ => todo!()
                        },
                        RuntimeValue::Dec(lhs) => match right {
                            RuntimeValue::Dec(rhs) => RuntimeValue::Dec(lhs - rhs),
                            _ => todo!()
                        },
                        _ => return Err(RuntimeError::OperandTypeError {
                            arity: 2,
                            operator: e.operator.clone(),
                            type_str: "numbers",
                        }),
                    },

                    "+" => match left {
                        RuntimeValue::Int(lhs) => match right {
                            RuntimeValue::Int(rhs) => RuntimeValue::Int(lhs + rhs),
                            _ => todo!()
                        },
                        RuntimeValue::Dec(lhs) => match right {
                            RuntimeValue::Dec(rhs) => RuntimeValue::Dec(lhs + rhs),
                            _ => todo!()
                        },
                        RuntimeValue::Str(lhs) => match right {
                            RuntimeValue::Str(rhs) => RuntimeValue::Str(lhs + &rhs),
                            _ => todo!()
                        },
                        _ => return Err(RuntimeError::OperandTypeError {
                            arity: 2,
                            operator: e.operator.clone(),
                            type_str: "two numbers or two strings",
                        }),
                    },

                    "/" => match left {
                        RuntimeValue::Int(lhs) => match right {
                            RuntimeValue::Int(rhs) => RuntimeValue::Int(lhs / rhs),
                            _ => todo!()
                        },
                        RuntimeValue::Dec(lhs) => match right {
                            RuntimeValue::Dec(rhs) => RuntimeValue::Dec(lhs / rhs),
                            _ => todo!()
                        },
                        _ => return Err(RuntimeError::OperandTypeError {
                            arity: 2,
                            operator: e.operator.clone(),
                            type_str: "numbers",
                        }),
                    },

                    "*" => match left {
                        RuntimeValue::Int(lhs) => match right {
                            RuntimeValue::Int(rhs) => RuntimeValue::Int(lhs * rhs),
                            _ => todo!()
                        },
                        RuntimeValue::Dec(lhs) => match right {
                            RuntimeValue::Dec(rhs) => RuntimeValue::Dec(lhs * rhs),
                            _ => todo!()
                        },
                        _ => return Err(RuntimeError::OperandTypeError {
                            arity: 2,
                            operator: e.operator.clone(),
                            type_str: "numbers",
                        }),
                    },

                    _ => todo!("unknown operator"),
                }
            } else {
                todo!("give error")
            }
        }
    })
}
