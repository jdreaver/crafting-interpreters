use std::env;
use std::io;

use lox::eval;
use lox::lexer;
use lox::parser;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    if args.len() != 1 {
        eprintln!("Usage: lox PROGRAM");
        std::process::exit(64);
    }

    let program = &args[0];

    let mut lexer = lexer::Lexer::new(program);
    match lexer.lex() {
        Ok(()) => {},
        Err(err) => {
            eprintln!("ERROR: {:#?}", err);
            std::process::exit(1);
        }
    }

    let mut parser = parser::Parser::new(lexer.tokens);
    let program = match parser.parse() {
        Ok(program) => program,
        Err(err) => {
            eprintln!("ERROR: {:#?}", err);
            std::process::exit(1);
        }
    };
    match eval::evaluate_program(program, &mut io::stdout()) {
        Ok(()) => {},
        Err(err) => {
            eprintln!("ERROR: {:#?}", err);
            std::process::exit(1);
        }
    }
}
