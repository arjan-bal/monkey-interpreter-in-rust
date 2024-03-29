use std::{
    fmt::{self, Display},
    rc::Rc,
};

use crate::token::Token;

macro_rules! expressions {
    ( $($type:ident),* ) => {
      pub enum Expression {
        $( $type($type),)*
      }

      impl Display for Expression {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let res = match &self {
                $( Expression::$type(x) => x.to_string(),)*
            };
            f.write_str(res.as_str())
        }
      }
    };
}

expressions!(
    Identifier,
    IntegerLiteral,
    Boolean,
    StringLiteral,
    ArrayLiteral,
    HashLiteral,
    CallExpression,
    IfExpression,
    FunctionLiteral,
    InfixExpression,
    PrefixExpression,
    IndexExpression
);


impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let res = match &self {
            Statement::LetStatement(x) => x.to_string(),
            Statement::ReturnStatement(x) => x.to_string(),
            Statement::ExpressionStatement(x) => x.to_string(),
        };
        f.write_str(res.as_str())
    }
}

pub enum Statement {
    LetStatement(LetStatement),
    ReturnStatement(ReturnStatement),
    ExpressionStatement(ExpressionStatement),
}

pub struct Program {
    pub statements: Vec<Statement>,
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

pub struct Identifier {
    pub token: Token,
    pub name: String,
}

impl Identifier {
    pub fn new(token: Token) -> Identifier {
        let name = if let Token::Ident(s) = &token {
            s.clone()
        } else {
            panic!(
                "Trying to create an Identifier with non-ident token {}",
                token
            );
        };
        Identifier { token, name }
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

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

pub struct StringLiteral {
    pub token: Token,
    pub value: String,
}

impl Display for StringLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl StringLiteral {
    pub fn new(token: Token) -> StringLiteral {
        let value = if let Token::String(x) = &token {
            x.clone()
        } else {
            panic!(
                "Trying to create a StringLiteral with non String token: {}",
                token
            );
        };
        StringLiteral { token, value }
    }
}

pub struct ArrayLiteral {
    pub token: Token,
    pub elements: Vec<Expression>,
}

impl Display for ArrayLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.elements
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub struct HashLiteral {
    pub token: Token,
    pub elements: Vec<(Expression, Expression)>,
}

impl Display for HashLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.elements
                .iter()
                .map(|e| format!("{}: {}", e.0.to_string(), e.1.to_string()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub struct IndexExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

impl Display for IndexExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

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

pub struct CallExpression {
    pub token: Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
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

pub struct PrefixExpression {
    pub token: Token,
    pub right: Box<Expression>,
}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.token, self.right)
    }
}

pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
    pub operator: Token,
}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.operator, self.right)
    }
}

impl InfixExpression {
    pub fn new(operator: Token, left: Expression, right: Expression) -> InfixExpression {
        InfixExpression {
            token: operator.clone(),
            left: Box::new(left),
            right: Box::new(right),
            operator,
        }
    }
}

pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
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

pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Rc<Vec<Identifier>>,
    pub body: Rc<BlockStatement>,
}

impl Display for FunctionLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ({}) {}",
            self.token,
            self.parameters
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(","),
            self.body
        )
    }
}

pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
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

pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} = {}", self.token, self.name, self.value)
    }
}

impl LetStatement {
    pub fn new(token: Token, identifier: Token, value: Expression) -> LetStatement {
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
                name,
            },
            value,
        }
    }
}

pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Expression,
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.token, self.return_value)
    }
}

pub struct ExpressionStatement {
    pub token: Token, // the first token of the expression
    pub expression: Expression,
}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}
