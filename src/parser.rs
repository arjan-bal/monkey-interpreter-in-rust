use std::{
    error::Error,
    fmt::{self, Display},
};

use crate::{
    ast::{LetStatement, Program, Statement},
    lexer::Lexer,
    token::Token,
};

pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

#[derive(Debug)]
pub struct ParseError(String);

impl Error for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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

    fn parse_let_statement(&mut self) -> Result<Box<dyn Statement>, ParseError> {
        let let_token = self.cur_token.take().unwrap();
        self.next_token();
        let ident_token = match self.cur_token {
            Some(Token::Ident(_)) => self.cur_token.take().unwrap(),
            _ => {
                return Err(ParseError(
                    "Let token not followed by an identifier.".to_owned(),
                ))
            }
        };
        self.next_token();
        if self.cur_token != Some(Token::Assign) {
            return Err(ParseError(format!(
                "Let statement doesn't contain assign token. Found: {:?}",
                self.cur_token
            )));
        }
        self.next_token();
        // Remove tokens till we see a semicolon.
        while self.cur_token != Some(Token::Semicolon) {
            self.next_token();
        }
        // Don't remove the semicolon. It's removed in parse_program().
        Ok(Box::new(LetStatement::new(let_token, ident_token)))
    }

    fn parse_statement(&mut self) -> Result<Box<dyn Statement>, ParseError> {
        match (self.cur_token.as_ref(), self.peek_token.as_ref()) {
            (Some(&Token::Let), _) => self.parse_let_statement(),
            _ => Err(ParseError(format!(
                "Unknown statement type. Found tokens {:?}, {:?}",
                self.cur_token, self.peek_token
            ))),
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut prog = Program::new();
        while self.cur_token != None && self.cur_token != Some(Token::EOF) {
            match self.parse_statement() {
                Ok(s) => prog.add_statement(s),
                Err(e) => return Err(e),
            }
            self.next_token();
        }
        Ok(prog)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{LetStatement, Node},
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
            res.is_ok(),
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
            let got_name = match let_statement.name().token() {
                Token::Ident(s) => s,
                _ => panic!(
                    "Expected token inside let statement to be am Identifier, found: {:?}",
                    let_statement.token()
                ),
            };
            assert_eq!(got_name, name)
        }
    }
}
