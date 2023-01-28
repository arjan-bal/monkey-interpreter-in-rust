use std::{
    error::Error,
    fmt::{self, Display},
};

use crate::{ast::Program, lexer::Lexer, token::Token};

pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

#[derive(Debug)]
pub struct ParseError {
    message: String,
}

impl Error for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut p = Parser {
            lexer,
            cur_token: None,
            peek_token: None,
        };
        p.next_token();
        p.next_token();
        p
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.take();
        self.peek_token = self.lexer.next();
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{LetStatement, Statement, Node},
        lexer::Lexer,
        token::Token,
    };

    use super::Parser;

    #[test]
    fn test_let_statement() {
        let input = r#"
let x = 5;
let y = 10;
let foobar = 838383;
"#;
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let res = p.parse_program();
        assert!(
            !res.is_ok(),
            "parsing program failed with error: {}",
            res.err().unwrap()
        );
        let program = res.unwrap();
        let statements = program.get_statements();
        assert_eq!(statements.len(), 3, "program doesn't contain 2 statements");
        let expected_identifiers = ["x", "y", "foobar"];

        for (idx, statement) in statements.iter().enumerate() {
            let name = expected_identifiers[idx];
            assert_eq!(statement.token().unwrap(), &Token::Let);
            let let_statement = statement
                .as_any()
                .downcast_ref::<LetStatement>()
                .expect("Statement is not a LetStatement!");
            assert_eq!(let_statement.name().value(), name);
            let got_name  = match let_statement.token().unwrap() {
                Token::Ident(s) => s,
                _ => panic!("token inside let statement isn't a Identifier!"),
            };
            assert_eq!(got_name, name);
        }
    }
}
