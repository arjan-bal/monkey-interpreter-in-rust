use std::{
    any::Any,
    fmt::{self, Display},
};

use crate::token::Token;
use node_macro_derive::NodeMacro;

pub trait Node: Display {
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

impl Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let res = self
            .statements
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        write!(f, "{}", res)
    }
}

impl Program {
    pub fn statements(&self) -> &'_ Vec<Box<(dyn Statement + '_)>> {
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

#[derive(NodeMacro)]
pub struct Identifier {
    token: Token,
    value: String,
}

impl Identifier {
    pub fn value(&self) -> &String {
        &self.value
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

impl Expression for Identifier {}

impl Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(NodeMacro)]
pub struct IntegerLiteral {
    token: Token,
    value: i64,
}

impl Display for IntegerLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl IntegerLiteral {
    pub fn new(token: Token) -> IntegerLiteral {
        let value = if let Token::Int(x) = token {
            x
        } else {
            panic!(
                "Trying to create an IntegerLiteral with non int token: {}",
                token
            );
        };
        IntegerLiteral { token, value }
    }

    pub fn value(&self) -> i64 {
        self.value
    }
}

impl Expression for IntegerLiteral {}

#[derive(NodeMacro)]
pub struct PrefixExpression {
    token: Token,
    right: Box<dyn Expression>,
}

impl Expression for PrefixExpression {}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.token, self.right)
    }
}

impl PrefixExpression {
    pub fn right(&self) -> &Box<dyn Expression> {
        &self.right
    }

    pub fn new(token: Token, exp: Box<dyn Expression>) -> PrefixExpression {
        PrefixExpression { token, right: exp }
    }
}

#[derive(NodeMacro)]
pub struct InfixExpression {
    token: Token,
    left: Box<dyn Expression>,
    right: Box<dyn Expression>,
    operator: Token,
}

impl Expression for InfixExpression {}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.operator(), self.right)
    }
}

impl InfixExpression {
    pub fn left(&self) -> &Box<dyn Expression> {
        &self.left
    }

    pub fn right(&self) -> &Box<dyn Expression> {
        &self.right
    }

    pub fn operator(&self) -> &Token {
        &self.operator
    }

    pub fn new(
        operator: Token,
        left: Box<dyn Expression>,
        right: Box<dyn Expression>,
    ) -> InfixExpression {
        InfixExpression {
            token: operator.clone(),
            left,
            right,
            operator,
        }
    }
}

pub struct LetStatement {
    token: Token,
    name: Identifier,
    // value: Box<dyn Expression>,
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} = TODO", self.token, self.name)
    }
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
                "LetStatement constructor called with non identifier token: {}",
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

#[derive(NodeMacro)]
pub struct ReturnStatement {
    token: Token,
    // return_value: Box<dyn Expression>,
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} TODO", self.token)
    }
}

impl Statement for ReturnStatement {}

impl ReturnStatement {
    pub fn new(token: Token) -> ReturnStatement {
        ReturnStatement { token }
    }
}

#[derive(NodeMacro)]
pub struct ExpressionStatement {
    token: Token, // the first token of the expression
    expression: Box<dyn Expression>,
}

impl Statement for ExpressionStatement {}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

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
