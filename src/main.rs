use std::{fs, io::{self, Write}};
use itertools::Itertools;

#[macro_use]
mod util;
mod errors;
mod text;
mod lexer;
mod parser;
mod interpreter;
mod traverser; // TODO: change or remove

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
            if let Err(run_file_err) = run_file(file) { match run_file_err {
                RunFileError::Io(e) => panic!("file not found?: {:?}", e),
                RunFileError::Code(stage) => match stage {
                    Stage::Parsing => std::process::exit(65),
                    Stage::Evaluating => std::process::exit(70),
                },
            } }
        },
        [_] => {
            run_prompt().expect("reading from stdin failed?");
        },
        [] => {
            panic!("This program is not designed for whatever this environment is.");
        },
    }
}

enum RunFileError {
    Io(io::Error),
    Code(Stage),
}
impl From<io::Error> for RunFileError {
    fn from(e: io::Error) -> Self { RunFileError::Io(e) }
}
impl From<Stage> for RunFileError {
    fn from(e: Stage) -> Self { RunFileError::Code(e) }
}

fn run_file(path: &str) -> Result<(), RunFileError> {
    let file = fs::read_to_string(path)?;
    run(file.as_str())?;
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
        let _ = run(s.as_str());
    }
}

enum Stage {
    Parsing,
    Evaluating,
}

fn run(source: &str) -> Result<(), Stage> {
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
        return Err(Stage::Parsing);
    }

    let expr = match parser::parse(&tokens) {
        Ok(expr) => {
            println!("{}", parser::print_ast(&expr));
            expr
        },
        Err(errors) => {
            if errors.len() == 1 {
                println!("An error ocurred:");
            } else {
                println!("Some errors ocurred:");
            }
            for e in errors {
                println!("{:?}", e);
            }
            return Err(Stage::Parsing);
        }
    };

    match interpreter::interpret(&expr) {
        Ok(value) => println!("{}", value),
        Err(e) => {
            println!("{}", e);
            return Err(Stage::Evaluating);
        }
    }

    Ok(())
}
