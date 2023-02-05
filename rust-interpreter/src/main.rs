use lexer::Lexer;
use std::io::{stdin, stdout, Write};

mod lexer;
mod token;
mod ast;
mod parser;

const PROMPT: &str = ">>";

fn main() {
    loop {
        print!("{} ", PROMPT);
        stdout().flush().unwrap();
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();
        let lex = Lexer::new(&input);
        for token in lex {
            println!("{}", token);
        }
    }
}
