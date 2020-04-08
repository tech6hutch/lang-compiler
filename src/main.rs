use std::{fs, io::{self, Write}};
use bigdecimal::BigDecimal;
use itertools::Itertools;
use num_bigint::BigInt;

#[macro_use]
mod util;
mod errors;
mod text;
mod lexer;
mod parser;
mod traverser;

// fn main() {
//     use lexer::{OperatorToken, OperatorKind};
//     use parser::{Expression as Expr, BinaryExpr, UnaryExpr, IntegerLiteral, DecimalLiteral};
//     let span = text::Span::one(text::Pos { line: 0, col: 0 });
//     let expr: Expr = Expr::Binary(BinaryExpr {
//         left: Box::new(Expr::Unary(UnaryExpr {
//             operator: OperatorToken {
//                 kind: OperatorKind::Other("-".to_string()),
//                 span,
//             },
//             right: Box::new(Expr::Int(IntegerLiteral { value: BigInt::from(123) })),
//         })),
//         operator: OperatorToken {
//             kind: OperatorKind::Other("*".to_string()),
//             span,
//         },
//         right: Box::new(Expr::Grouping(Box::new(Expr::Dec(DecimalLiteral { value: "45.67".parse().unwrap() })))),
//     });
//     let printed = parser::print_ast(&expr);
//     assert_eq!(printed, "(* (- 123) (group 45.67))");
//     println!("{}", printed);
// }

fn main() {
    let args = std::env::args().collect_vec();
    match args.as_slice() {
        [_, _, _, ..] => {
            println!("Usage: lang-compiler [file]");
            std::process::exit(64);
        },
        [_, file] => {
            run_file(file).expect("file not found?");
        },
        [_] => {
            run_prompt().expect("reading from stdin failed?");
        },
        [] => {
            panic!("This program is not designed for whatever this environment is.");
        },
    }
}

fn run_file(path: &str) -> io::Result<()> {
    let file = fs::read_to_string(path)?;
    run(file.as_str());
    Ok(())
}

fn run_prompt() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut s = String::new();
    loop {
        print!("> ");
        stdout.flush()?;
        s.clear();
        stdin.read_line(&mut s)?;
        run(s.as_str());
    }
}

fn run(source: &str) {
    let tokens = lexer::lex(source);

    for token in tokens.tokens() {
        println!("{}", token);
    }
    if tokens.has_errors() {
        let errors = tokens.errors();
        if errors.len() == 1 {
            println!("An error ocurred:");
        } else {
            println!("Some errors ocurred:");
        }
        for e in errors {
            println!("{:?}", e);
        }
    }
    
    match parser::parse(&tokens) {
        Ok(expr) => println!("{}", parser::print_ast(&expr)),
        Err(errors) => {
            if errors.len() == 1 {
                println!("An error ocurred:");
            } else {
                println!("Some errors ocurred:");
            }
            for e in errors {
                println!("{:?}", e);
            }
        }
    }
}
