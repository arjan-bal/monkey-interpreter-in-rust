use std::{
    any::Any,
    fmt::{self, Display},
};

use crate::token::Token;
use node_macro_derive::NodeMacro;

pub type BoxExpression = Box<dyn Expression>;

pub trait Node: Display {
    fn token(&self) -> Option<&Token>;
    fn as_any(&self) -> &dyn Any; // Required only for downcast during tests.
}

pub trait Expression: Node {}

pub trait Statement: Node {}

pub struct Program {
    pub statements: Vec<Box<dyn Statement>>,
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

#[derive(NodeMacro)]
pub struct Identifier {
    token: Token,
    pub value: String,
}

impl Identifier {
    pub fn new(token: Token) -> Identifier {
        let value = if let Token::Ident(s) = &token {
            s.clone()
        } else {
            panic!(
                "Trying to create an Identifier with non-ident token {}",
                token
            );
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
    pub token: Token,
    pub value: i64,
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
}

impl Expression for IntegerLiteral {}

#[derive(NodeMacro)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Boolean {
    pub fn new(token: Token) -> Boolean {
        let value = match token {
            Token::True => true,
            Token::False => false,
            _ => panic!("Trying to create Boolean from non bool token {}", token),
        };
        Boolean { token, value }
    }
}

impl Expression for Boolean {}

#[derive(NodeMacro)]
pub struct CallExpression {
    pub token: Token,
    pub function: BoxExpression,
    pub arguments: Vec<BoxExpression>,
}

impl Display for CallExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.function,
            self.arguments
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl Expression for CallExpression {}

#[derive(NodeMacro)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: BoxExpression,
}

impl Expression for PrefixExpression {}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.token, self.right)
    }
}

#[derive(NodeMacro)]
pub struct InfixExpression {
    pub token: Token,
    pub left: BoxExpression,
    pub right: BoxExpression,
    pub operator: Token,
}

impl Expression for InfixExpression {}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.operator, self.right)
    }
}

impl InfixExpression {
    pub fn new(operator: Token, left: BoxExpression, right: BoxExpression) -> InfixExpression {
        InfixExpression {
            token: operator.clone(),
            left,
            right,
            operator,
        }
    }
}

#[derive(NodeMacro)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Box<dyn Statement>>,
}

impl Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self
            .statements
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        write!(f, "{}", s)
    }
}

#[derive(NodeMacro)]
pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Display for FunctionLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ({}) {}",
            self.token().unwrap(),
            self.parameters
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(","),
            self.body
        )
    }
}

impl Expression for FunctionLiteral {}

#[derive(NodeMacro)]
pub struct IfExpression {
    pub token: Token,
    pub condition: BoxExpression,
    pub consequence: BlockStatement,
    pub alternate: Option<BlockStatement>,
}

impl Display for IfExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = format!(
            "if ({})\n{}{}",
            self.condition,
            self.consequence,
            self.alternate
                .as_ref()
                .map_or("".to_owned(), |a| format!("\n{}", a))
        );
        write!(f, "{}", s)
    }
}

impl Expression for IfExpression {}

pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: BoxExpression,
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} = {}", self.token, self.name, self.value)
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
    pub fn new(token: Token, identifier: Token, value: BoxExpression) -> LetStatement {
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
            value,
        }
    }
}

#[derive(NodeMacro)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: BoxExpression,
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.token, self.return_value)
    }
}

impl Statement for ReturnStatement {}

#[derive(NodeMacro)]
pub struct ExpressionStatement {
    pub token: Token, // the first token of the expression
    pub expression: BoxExpression,
}

impl Statement for ExpressionStatement {}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}
