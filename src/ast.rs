use std::{any::Any, fmt::Debug};

use crate::token::Token;

pub trait Node: Debug {
    fn token(&self) -> Option<&Token>;
    fn as_any(&self) -> &dyn Any; // Required only for downcast during tests.
}

pub trait Expression: Node {}

pub trait Statement: Node {}

#[derive(Debug)]
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

#[derive(Debug)]
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

    pub fn new(token: Token) -> Identifier {
      let value = if let Token::Ident(s) = &token {
        s.clone()
      } else {
        panic!("Trying to create an Identifier with non-ident token");
      };
      Identifier { token, value }
    }
}

impl Node for Identifier {
    fn token(&self) -> Option<&Token> {
        Some(&self.token)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for Identifier {}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct ReturnStatement {
    token: Token,
    // return_value: Box<dyn Expression>,
}

impl Statement for ReturnStatement {}

impl Node for ReturnStatement {
    fn token(&self) -> Option<&Token> {
        Some(&self.token)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ReturnStatement {
    pub fn new(token: Token) -> ReturnStatement {
        ReturnStatement { token }
    }
}

#[derive(Debug)]
pub struct ExpressionStatement {
    token: Token, // the first token of the expression
    expression: Box<dyn Expression>,
}

impl Node for ExpressionStatement {
    fn token(&self) -> Option<&Token> {
        Some(&self.token)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Statement for ExpressionStatement {}

impl ExpressionStatement {
    pub fn expression(&self) -> &Box<dyn Expression> {
        &self.expression
    }

    pub fn new(token: Token, exp: Box<dyn Expression>) -> ExpressionStatement {
        ExpressionStatement {
            token,
            expression: exp,
        }
    }
}
