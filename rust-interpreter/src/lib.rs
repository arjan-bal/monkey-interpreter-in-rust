mod ast;
mod evaluator;
mod lexer;
mod object;
mod parser;
mod token;

use std::error::Error;

use ast::Program;
use evaluator::eval_program;
use lexer::Lexer;
use object::{Environment, MutableEnvironment};
use parser::Parser;

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

pub struct Interpreter {
    environment: MutableEnvironment,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            environment: Environment::new(),
        }
    }

    pub fn interpret(&mut self, input: String) -> String {
        let lex = Lexer::new(&input);
        let mut parser = Parser::new(lex);
        match parser.parse_program() {
            Err(e) => Self::format_error(Box::new(e)),
            Ok(p) => self.evaluate_program(p),
        }
    }

    fn format_error(error: Box<dyn Error>) -> String {
        format!(
            "{}\nWhoops! We ran into some monkey business here!\n  errors:\n{}",
            MONKEY_FACE, error
        )
    }

    fn evaluate_program(&self, program: Program) -> String {
        match eval_program(&program, &self.environment) {
            Ok(evaluated) => format!("{}", evaluated.inspect()),
            Err(e) => Self::format_error(Box::new(e)),
        }
    }
}
