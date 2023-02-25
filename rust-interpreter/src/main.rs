use ast::Program;
use evaluator::eval;
use lexer::Lexer;
use parser::ParseErrors;
use std::io::{stdin, stdout, Write};

use crate::parser::Parser;

mod ast;
mod lexer;
mod parser;
mod token;
mod object;
mod evaluator;

const GREETING_MESSAGE: &str = "Hello mrnugget! This is the Monkey programming language!\nFeel free to type in commands";
const PROMPT: &str = ">>";
const MONKEY_FACE: &str = r#"
            __,__
   .--.  .-"     "-.  .--.
  / .. \/  .-. .-.  \/ .. \
 | |  '|  /   Y   \  |'  | |
 | \   \  \ 0 | 0 /  /   / |
  \ '- ,\.-"""""""-./, -' /
   ''-' /_   ^ ^   _\ '-''
       |  \._   _./  |
       \   \ '~' /   /
        '._ '-=-' _.'
           '-----'
"#;

fn main() {
    println!("{}", GREETING_MESSAGE);
    loop {
        print!("{} ", PROMPT);
        stdout().flush().unwrap();
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();
        let lex = Lexer::new(&input);
        let mut parser = Parser::new(lex);
        match parser.parse_program() {
            Err(e) => print_error(e),
            Ok(p) => eval_program(p),
        };
    }
}

fn print_error(errors: ParseErrors) {
    println!("{}", MONKEY_FACE);
    println!("Whoops! We ran into some monkey business here!");
    println!(" parser errors:");

    for err in errors.0 {
        println!("\t{}", err);
    }
}

fn eval_program(program: Program) {
    let evaluated = eval(&ast::Node::Program(program));
    println!("{}", evaluated.inspect());
}
