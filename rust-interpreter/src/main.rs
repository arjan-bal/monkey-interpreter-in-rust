use monkeyinterpreter::Interpreter;
use std::io::{stdin, stdout, Write};

const GREETING_MESSAGE: &str =
    "Hello mrnugget! This is the Monkey programming language!\nFeel free to type in commands";
const PROMPT: &str = ">>";

fn main() {
    println!("{}", GREETING_MESSAGE);
    let mut interpreter = Interpreter::new();
    loop {
        print!("{} ", PROMPT);
        stdout().flush().unwrap();
        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();
        println!("{}", interpreter.interpret(input));
    }
}
