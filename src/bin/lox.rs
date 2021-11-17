use std::env;

use lox::lexer;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    if args.len() != 1 {
        eprintln!("Usage: lox PROGRAM");
        std::process::exit(64);
    }

    let program = &args[0];
    let mut lexer = lexer::Lexer::new(program);
    match lexer.lex() {
        Ok(()) => println!("{:#?}", lexer.tokens),
        Err(err) => {
            eprintln!("ERROR: {:#?}", err);
            std::process::exit(1);
        }
    }
}
