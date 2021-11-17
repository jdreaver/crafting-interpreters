use std::env;

use lox::lexer;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();

    if args.len() != 1 {
        eprintln!("Usage: lox PROGRAM");
        std::process::exit(64);
    }

    let program = &args[0];
    println!("{:#?}", lexer::lex(program));
}
