use std::{
    error::Error,
    fmt::{self, Display},
};

use crate::{
    ast::{LetStatement, Program, ReturnStatement, Statement},
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

#[derive(Debug)]
pub struct ParseErrors(Vec<ParseError>);

impl Error for ParseErrors {}

impl Display for ParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
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
        let ident_token = self.get_ident_token()?;
        self.expect_peek(Token::Assign)?;
        self.next_token(); // cur is not assign.
        self.next_token(); // skip assign.

        // Remove tokens till we see a semicolon.
        while self.cur_token != Some(Token::Semicolon) {
            self.next_token();
        }
        // Don't remove the semicolon. It's removed in parse_program().
        Ok(Box::new(LetStatement::new(let_token, ident_token)))
    }

    fn parse_return_statement(&mut self) -> Result<Box<dyn Statement>, ParseError> {
        let return_token = self.cur_token.take().unwrap();
        self.next_token();
        // Remove tokens till we see a semicolon.
        while self.cur_token != Some(Token::Semicolon) {
            self.next_token();
        }
        // Don't remove the semicolon. It's removed in parse_program().
        Ok(Box::new(ReturnStatement::new(return_token)))
    }

    fn get_ident_token(&mut self) -> Result<Token, ParseError> {
        let ident_token = match self.cur_token {
            Some(Token::Ident(_)) => self.cur_token.take().unwrap(),
            _ => {
                return Err(ParseError(format!(
                    "Expected an identifier token, but found: {:?}",
                    self.cur_token.as_ref()
                )))
            }
        };
        Ok(ident_token)
    }

    fn expect_peek(&mut self, expected: Token) -> Result<(), ParseError> {
        if self.peek_token.as_ref() != Some(&expected) {
            return Err(ParseError(format!(
                "Expected next token {:?}, found: {:?}",
                &expected, self.peek_token
            )));
        }
        self.next_token();
        Ok(())
    }

    fn parse_statement(&mut self) -> Result<Box<dyn Statement>, ParseError> {
        match (self.cur_token.as_ref(), self.peek_token.as_ref()) {
            (Some(&Token::Let), _) => self.parse_let_statement(),
            (Some(&Token::Return), _) => self.parse_return_statement(),
            _ => Err(ParseError(format!(
                "Unknown statement type. Found tokens {:?}, {:?}",
                self.cur_token, self.peek_token
            ))),
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseErrors> {
        let mut prog = Program::new();
        let mut parse_errors = Vec::new();
        while self.cur_token != None && self.cur_token != Some(Token::EOF) {
            match self.parse_statement() {
                Ok(s) => prog.add_statement(s),
                Err(e) => parse_errors.push(e),
            }
            self.next_token();
        }
        if parse_errors.is_empty() {
            Ok(prog)
        } else {
            Err(ParseErrors(parse_errors))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{LetStatement, Node, ReturnStatement},
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
        assert_eq!(statements.len(), 3, "program doesn't contain 3 statements");
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
            assert_eq!(got_name, name);
        }
    }

    #[test]
    fn test_return_statement() {
        let input = r#"
return 5;
return 10;
return 993322;
"#;
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let res = p.parse_program();
        assert!(
            res.is_ok(),
            "parsing program failed with errors: {}",
            res.err().unwrap()
        );
        let program = res.unwrap();
        let statements = program.get_statements();
        assert_eq!(statements.len(), 3, "program doesn't contain 3 statements");

        for statement in statements.iter() {
            assert_eq!(statement.token().unwrap(), &Token::Return);
            statement
                .as_any()
                .downcast_ref::<ReturnStatement>()
                .expect("Statement is not a ReturnStatement!");
        }
    }
}
