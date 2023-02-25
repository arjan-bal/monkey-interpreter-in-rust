use ast::Program;
use evaluator::eval;
use lexer::Lexer;
use std::{
    error::Error,
    io::{stdin, stdout, Write},
};

use crate::{parser::Parser, object::Environment};

mod ast;
mod evaluator;
mod lexer;
mod object;
mod parser;
mod token;

const GREETING_MESSAGE: &str =
    "Hello mrnugget! This is the Monkey programming language!\nFeel free to type in commands";
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
    let mut env = Environment::new();
    loop {
        print!("{} ", PROMPT);
        stdout().flush().unwrap();
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();
        let lex = Lexer::new(&input);
        let mut parser = Parser::new(lex);
        match parser.parse_program() {
            Err(e) => print_error(Box::new(e)),
            Ok(p) => eval_program(p, &mut env),
        };
    }
}

fn print_error(error: Box<dyn Error>) {
    println!("{}", MONKEY_FACE);
    println!("Whoops! We ran into some monkey business here!");
    println!(" error:\n{}", error);
}

fn eval_program(program: Program, env: &mut Environment) {
    match eval(&ast::Node::Program(program), env) {
        Ok(evaluated) => println!("{}", evaluated.inspect()),
        Err(e) => print_error(Box::new(e)),
    }
}
