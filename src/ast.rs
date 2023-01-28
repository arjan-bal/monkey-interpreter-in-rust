use std::any::Any;

use crate::token::Token;

pub trait Node {
    fn token(&self) -> Option<&Token>;
    fn as_any(&self) -> &dyn Any; // Required only for downcast during tests.
}

pub trait Expression: Node {}

pub trait Statement: Node {}

pub struct Program {
    statements: Vec<Box<dyn Statement>>,
}

impl Node for Program {
    fn token(&self) -> Option<&Token> {
        if self.statements.is_empty() {
            return None;
        }
        self.statements[0].token()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Program {
    pub fn get_statements(&self) -> &'_ Vec<Box<(dyn Statement + '_)>> {
        &self.statements
    }

    pub fn add_statement(&mut self, statement: Box<dyn Statement>) {
        self.statements.push(statement);
    }

    pub fn new() -> Program {
        Program {
            statements: Vec::new(),
        }
    }
}

pub struct Identifier {
    token: Token,
    value: String,
}

impl Identifier {
    pub fn value(&self) -> &String {
        &self.value
    }
    pub fn token(&self) -> &Token {
        &self.token
    }
}

pub struct LetStatement {
    token: Token,
    name: Identifier,
    // value: Box<dyn Expression>,
}

impl Statement for LetStatement {}

impl Node for LetStatement {
    fn token(&self) -> Option<&Token> {
        Some(&self.token)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl LetStatement {
    pub fn name(&self) -> &Identifier {
        &self.name
    }

    pub fn new(token: Token, identifier: Token) -> LetStatement {
        let name = match &identifier {
            Token::Ident(name) => name.clone(),
            _ => panic!(
                "LetStatement constructor called with non identifier token: {:?}",
                identifier
            ),
        };
        LetStatement {
            token,
            name: Identifier {
                token: identifier,
                value: name,
            },
        }
    }
}
