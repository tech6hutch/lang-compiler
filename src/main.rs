use std::{fs, io::{self, Write}};
use itertools::Itertools;

mod errors;
mod text;
mod lexer;
// mod parser;
mod traverser;
mod util;

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
        println!("{:?}", token);
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
}
