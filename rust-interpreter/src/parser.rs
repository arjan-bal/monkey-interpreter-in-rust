use std::{
    collections::HashMap,
    error::Error,
    fmt::{self, Display},
    rc::Rc,
};

use crate::{
    ast::{
        BlockStatement, Boolean, CallExpression, Expression, ExpressionStatement, FunctionLiteral,
        Identifier, IfExpression, InfixExpression, IntegerLiteral, LetStatement, PrefixExpression,
        Program, ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::Token,
};

type ParseExpressionResult = Result<Expression, ParseError>;
type PrefixParseFn = Box<dyn Fn(&mut ParserInternal, &ParsingContext) -> ParseExpressionResult>;
type InfixParseFn =
    Box<dyn Fn(&mut ParserInternal, Expression, &ParsingContext) -> ParseExpressionResult>;

struct ParserInternal {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

pub struct Parser {
    ctx: ParsingContext,
    parser: ParserInternal,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut ctx = ParsingContext::new();
        let parser = ParserInternal::new(lexer, &mut ctx);
        Parser { ctx, parser }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseErrors> {
        self.parser.parse_program(&self.ctx)
    }
}

// This is needed to hold the expression parsing functions because the functions need
// to be passed a mutable reference to the Parser. If this is part of the parser, referring
// to a function will require an immutable ref to parser and we can't have a mutable and immutable
// ref to parser at the same time.
struct ParsingContext {
    prefix_parse_fns: HashMap<Token, PrefixParseFn>,
    infix_parse_fns: HashMap<Token, InfixParseFn>,
    precedence_map: HashMap<Token, Precedence>,
}

impl ParsingContext {
    fn register_prefix(&mut self, token: &Token, func: PrefixParseFn) {
        self.prefix_parse_fns.insert(token.clone(), func);
    }

    fn register_infix(&mut self, token: &Token, func: InfixParseFn) {
        self.infix_parse_fns.insert(token.clone(), func);
    }

    fn new() -> ParsingContext {
        let precedence_map = HashMap::from([
            (Token::EQ, Precedence::Equals),
            (Token::NotEq, Precedence::Equals),
            (Token::LT, Precedence::LessGreater),
            (Token::GT, Precedence::LessGreater),
            (Token::Plus, Precedence::Sum),
            (Token::Minus, Precedence::Sum),
            (Token::Slash, Precedence::Product),
            (Token::Asterisk, Precedence::Product),
            (Token::LParen, Precedence::Call),
        ]);
        ParsingContext {
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
            precedence_map,
        }
    }
}

#[derive(Debug)]
pub struct ParseError(String);

impl Error for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, PartialOrd, Debug)]
enum Precedence {
    Lowest,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // myFunction(X)
}

#[derive(Debug)]
pub struct ParseErrors(pub Vec<ParseError>);

impl Error for ParseErrors {}

impl Display for ParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|e| e.0.to_string())
                .collect::<Vec<String>>()
                .join("\n")
        )
    }
}

impl ParserInternal {
    pub fn new(lexer: Lexer, ctx: &mut ParsingContext) -> ParserInternal {
        let mut p = ParserInternal {
            lexer,
            cur_token: None,
            peek_token: None,
        };
        p.next_token();
        p.next_token();
        let mut prefix_fns = Vec::from([
            (
                ParserInternal::parse_identifier(),
                Token::Ident(String::from("")),
            ),
            (ParserInternal::parse_integer_literal(), Token::Int(0)),
            (ParserInternal::parse_boolean_literal(), Token::True),
            (ParserInternal::parse_boolean_literal(), Token::False),
            (
                ParserInternal::parse_prefix_operator_expressions(),
                Token::Bang,
            ),
            (
                ParserInternal::parse_prefix_operator_expressions(),
                Token::Minus,
            ),
            (ParserInternal::parse_grouped_expression(), Token::LParen),
            (ParserInternal::parse_if_expression(), Token::If),
            (ParserInternal::parse_function_literal(), Token::Function),
        ]);
        while !prefix_fns.is_empty() {
            let (func, token) = prefix_fns.pop().unwrap();
            ctx.register_prefix(&token.get_representative_token(), func);
        }

        let mut infix_fns = Vec::from([
            (ParserInternal::parse_infix_expressions(), Token::Plus),
            (ParserInternal::parse_infix_expressions(), Token::Minus),
            (ParserInternal::parse_infix_expressions(), Token::Slash),
            (ParserInternal::parse_infix_expressions(), Token::Asterisk),
            (ParserInternal::parse_infix_expressions(), Token::EQ),
            (ParserInternal::parse_infix_expressions(), Token::NotEq),
            (ParserInternal::parse_infix_expressions(), Token::LT),
            (ParserInternal::parse_infix_expressions(), Token::GT),
            (ParserInternal::parse_call_expression(), Token::LParen),
        ]);
        while !infix_fns.is_empty() {
            let (func, token) = infix_fns.pop().unwrap();
            ctx.register_infix(&token.get_representative_token(), func);
        }
        p
    }

    fn parse_identifier() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, _: &ParsingContext| {
            let ident = parser.cur_token.as_ref().unwrap().clone();
            Ok(Expression::Identifier(Identifier::new(ident)))
        };
        Box::new(f)
    }

    fn parse_integer_literal() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, _: &ParsingContext| {
            let integer_literal = parser.cur_token.as_ref().unwrap().clone();
            Ok(Expression::IntegerLiteral(IntegerLiteral::new(
                integer_literal,
            )))
        };
        Box::new(f)
    }

    fn parse_boolean_literal() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, _: &ParsingContext| {
            let boolean_literal = parser.cur_token.as_ref().unwrap().clone();
            Ok(Expression::Boolean(Boolean::new(boolean_literal)))
        };
        Box::new(f)
    }

    fn parse_prefix_operator_expressions() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, ctx: &ParsingContext| {
            let token = parser.cur_token.take().unwrap();
            parser.next_token();
            let right_expression = parser.parse_expression(Precedence::Prefix, ctx)?;
            Ok(Expression::PrefixExpression(PrefixExpression {
                token,
                right: Box::new(right_expression),
            }))
        };
        Box::new(f)
    }

    fn parse_grouped_expression() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, ctx: &ParsingContext| {
            parser.next_token();
            let expression = parser.parse_expression(Precedence::Lowest, ctx)?;
            parser.expect_peek(Token::RParen)?;
            Ok(expression)
        };
        Box::new(f)
    }

    fn parse_if_expression() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, ctx: &ParsingContext| {
            let token = parser.cur_token.take().unwrap();
            parser.expect_peek(Token::LParen)?;
            parser.next_token();
            let condition = parser.parse_expression(Precedence::Lowest, ctx)?;
            parser.expect_peek(Token::RParen)?;
            parser.expect_peek(Token::LBrace)?;
            let consequence = parser.parse_block_statement(ctx)?;
            let mut alternate = None;

            if parser.peek_token == Some(Token::Else) {
                parser.next_token();
                parser.expect_peek(Token::LBrace)?;
                alternate = Some(parser.parse_block_statement(ctx)?);
            }

            Ok(Expression::IfExpression(IfExpression {
                token,
                condition: Box::new(condition),
                consequence,
                alternate,
            }))
        };
        Box::new(f)
    }

    fn parse_function_literal() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, ctx: &ParsingContext| {
            let token = parser.cur_token.take().unwrap();
            parser.expect_peek(Token::LParen)?;
            let parameters = parser.parse_parameters()?;
            parser.expect_peek(Token::LBrace)?;
            let body = parser.parse_block_statement(ctx)?;
            Ok(Expression::FunctionLiteral(FunctionLiteral {
                token,
                parameters: Rc::new(parameters),
                body: Rc::new(body),
            }))
        };
        Box::new(f)
    }

    fn parse_infix_expressions() -> InfixParseFn {
        let f = |parser: &mut ParserInternal, left: Expression, ctx: &ParsingContext| {
            let precedence = parser.cur_precedence(ctx);
            let operator = parser.cur_token.take().unwrap();
            parser.next_token();
            let right = parser.parse_expression(precedence, ctx)?;
            Ok(Expression::InfixExpression(InfixExpression::new(
                operator, left, right,
            )))
        };
        Box::new(f)
    }

    fn parse_call_expression() -> InfixParseFn {
        let f = |parser: &mut ParserInternal, left: Expression, ctx: &ParsingContext| {
            let token = parser.cur_token.take().unwrap();
            let arguments = parser.parse_arguments(ctx)?;
            Ok(Expression::CallExpression(CallExpression {
                token,
                function: Box::new(left),
                arguments,
            }))
        };
        Box::new(f)
    }

    fn parse_arguments(&mut self, ctx: &ParsingContext) -> Result<Vec<Expression>, ParseError> {
        self.next_token(); // Skip the LParen.
        let mut arguments = Vec::new();
        if self.cur_token == Some(Token::RParen) {
            return Ok(arguments);
        }

        // Remove at least one parameter.
        arguments.push(self.parse_expression(Precedence::Lowest, ctx)?);

        while self.peek_token == Some(Token::Comma) {
            self.next_token();
            self.next_token();
            arguments.push(self.parse_expression(Precedence::Lowest, ctx)?);
        }

        self.expect_peek(Token::RParen)?;
        Ok(arguments)
    }

    fn token_precedence(token: &Token, ctx: &ParsingContext) -> Precedence {
        ctx.precedence_map
            .get(token)
            .map_or(Precedence::Lowest, |p| p.clone())
    }

    fn cur_precedence(&self, ctx: &ParsingContext) -> Precedence {
        ParserInternal::token_precedence(self.cur_token.as_ref().unwrap(), ctx)
    }

    fn peek_precedence(&self, ctx: &ParsingContext) -> Precedence {
        ParserInternal::token_precedence(self.peek_token.as_ref().unwrap(), ctx)
    }

    fn parse_expression(
        &mut self,
        precedence: Precedence,
        ctx: &ParsingContext,
    ) -> ParseExpressionResult {
        let prefix_fn = ctx
            .prefix_parse_fns
            .get(&self.cur_token.as_ref().unwrap().get_representative_token())
            .ok_or(ParseError(format!(
                "prefix function not found for token: {:?}",
                self.cur_token
            )))?;
        let mut left = prefix_fn(self, ctx)?;
        while self.peek_token != Some(Token::Semicolon) && precedence < self.peek_precedence(ctx) {
            let f = match ctx.infix_parse_fns.get(self.peek_token.as_ref().unwrap()) {
                Some(f) => f,
                None => return Ok(left),
            };
            self.next_token();
            left = f(self, left, ctx)?;
        }
        Ok(left)
    }

    fn parse_expression_statement(
        &mut self,
        ctx: &ParsingContext,
    ) -> Result<Statement, ParseError> {
        let first_token = self
            .cur_token
            .as_ref()
            .ok_or(ParseError(format!(
                "Found empty cur token while parsing expression"
            )))?
            .clone();
        let expression = self.parse_expression(Precedence::Lowest, ctx)?;
        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }
        Ok(Statement::ExpressionStatement(ExpressionStatement {
            token: first_token,
            expression,
        }))
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.take();
        self.peek_token = self.lexer.next();
    }

    fn parse_let_statement(&mut self, ctx: &ParsingContext) -> Result<Statement, ParseError> {
        let let_token = self.cur_token.take().unwrap();
        self.next_token();
        let ident_token = self.get_ident_token()?;
        self.expect_peek(Token::Assign)?;
        self.next_token(); // cur is not assign.
        let value = self.parse_expression(Precedence::Lowest, ctx)?;
        // Don't remove the semicolon. It's removed in parse_program().
        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }
        Ok(Statement::LetStatement(LetStatement::new(
            let_token,
            ident_token,
            value,
        )))
    }

    fn parse_return_statement(&mut self, ctx: &ParsingContext) -> Result<Statement, ParseError> {
        let token = self.cur_token.take().unwrap();
        self.next_token();
        let return_value = self.parse_expression(Precedence::Lowest, ctx)?;
        // Don't remove the semicolon. It's removed in parse_program().
        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }
        Ok(Statement::ReturnStatement(ReturnStatement {
            token,
            return_value,
        }))
    }

    fn get_ident_token(&mut self) -> Result<Token, ParseError> {
        let ident_token = self.cur_token.take().ok_or(ParseError(format!(
            "Expected an identifier token, but found: {:?}",
            self.cur_token.as_ref()
        )))?;
        if !ident_token.is_ident() {
            Err(ParseError(format!(
                "Expected an identifier token, but found: {}",
                ident_token
            )))
        } else {
            Ok(ident_token)
        }
    }

    fn expect_peek(&mut self, expected: Token) -> Result<(), ParseError> {
        if self.peek_token.as_ref() != Some(&expected) {
            return Err(ParseError(format!(
                "Expected next token {}, found: {:?}",
                &expected, self.peek_token
            )));
        }
        self.next_token();
        Ok(())
    }

    fn parse_block_statement(
        &mut self,
        ctx: &ParsingContext,
    ) -> Result<BlockStatement, ParseError> {
        let mut statements = Vec::new();
        let token = self.cur_token.take().unwrap();
        self.next_token();
        while self.cur_token != Some(Token::RBrace) && self.cur_token != Some(Token::EOF) {
            let statement = self.parse_statement(ctx)?;
            statements.push(statement);
            self.next_token();
        }
        Ok(BlockStatement { token, statements })
    }

    fn parse_parameters(&mut self) -> Result<Vec<Identifier>, ParseError> {
        self.next_token(); // Skip the LParen.
        let mut identifiers = Vec::new();
        if self.cur_token == Some(Token::RParen) {
            return Ok(identifiers);
        }

        // Remove at least one parameter.
        identifiers.push(Identifier::new(self.cur_token.take().unwrap()));

        while self.peek_token == Some(Token::Comma) {
            self.next_token();
            self.next_token();
            identifiers.push(Identifier::new(self.cur_token.take().unwrap()));
        }

        self.expect_peek(Token::RParen)?;
        Ok(identifiers)
    }

    fn parse_statement(&mut self, ctx: &ParsingContext) -> Result<Statement, ParseError> {
        match (self.cur_token.as_ref(), self.peek_token.as_ref()) {
            (Some(&Token::Let), _) => self.parse_let_statement(ctx),
            (Some(&Token::Return), _) => self.parse_return_statement(ctx),
            _ => self.parse_expression_statement(ctx),
        }
    }

    fn parse_program(&mut self, ctx: &ParsingContext) -> Result<Program, ParseErrors> {
        let mut prog = Program {
            statements: Vec::new(),
        };
        let mut parse_errors = Vec::new();
        while self.cur_token != None && self.cur_token != Some(Token::EOF) {
            match self.parse_statement(ctx) {
                Ok(s) => prog.statements.push(s),
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
        ast::{Expression, ExpressionStatement, Identifier, Program, Statement},
        lexer::Lexer,
        parser::Parser,
        token::Token,
    };

    use super::ParseErrors;

    impl Statement {
        pub fn token(&self) -> Option<&Token> {
            match &self {
                Statement::LetStatement(x) => Some(&x.token),
                Statement::ReturnStatement(x) => Some(&x.token),
                Statement::ExpressionStatement(x) => Some(&x.token),
            }
        }
    }

    fn check_parse_errors(res: Result<Program, ParseErrors>) -> Program {
        assert!(
            res.is_ok(),
            "parsing program failed with error: {}",
            res.err().unwrap()
        );
        res.unwrap()
    }

    #[test]
    fn test_let_statement() {
        let input = r#"
let x = 5;
let y = true;
let foobar = 838383;
"#;
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 3, "program doesn't contain 3 statements");
        let expected_identifiers = ["x", "y", "foobar"];
        let expected_rhs = ["5", "true", "838383"];

        for (idx, statement) in statements.iter().enumerate() {
            let name = expected_identifiers[idx];
            assert_eq!(statement.token().unwrap(), &Token::Let);
            let let_statement = if let Statement::LetStatement(s) = statement {
                s
            } else {
                panic!("Statement {} is not a LetStatement!", statement)
            };
            assert_eq!(let_statement.name.name, name);
            let got_name = match &let_statement.name.token {
                Token::Ident(s) => s,
                _ => panic!(
                    "Expected token inside let statement to be am Identifier, found: {:?}",
                    let_statement.token
                ),
            };
            assert_eq!(got_name, name);
            assert_eq!(let_statement.value.to_string(), expected_rhs[idx]);
        }
    }

    #[test]
    fn test_return_statement() {
        let input = r#"
return 5;
return true;
return 993322;
"#;
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 3, "program doesn't contain 3 statements");
        let expected_rhs = ["5", "true", "993322"];

        for (idx, statement) in statements.iter().enumerate() {
            assert_eq!(statement.token().unwrap(), &Token::Return);
            let return_statement = if let Statement::ReturnStatement(s) = statement {
                s
            } else {
                panic!("Statement {} is not a ReturnStatement!", statement)
            };
            assert_eq!(return_statement.return_value.to_string(), expected_rhs[idx]);
        }
    }

    fn check_expression_statement<'a>(statement: &'a Statement) -> &'a ExpressionStatement {
        if let Statement::ExpressionStatement(s) = statement {
            s
        } else {
            panic!("Statement {} is not a ExpressionStatement!", statement)
        }
    }

    #[test]
    fn test_identifier_expressions() {
        let input = "foobar;";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        test_identifier_expression(&expression_statement.expression, "foobar");
    }

    fn test_identifier_expression(expression: &Expression, name: &str) {
        if let Expression::Identifier(e) = expression {
            test_identifier(e, name)
        } else {
            panic!("Expression {} is not a Identifier!", expression)
        }
    }

    fn test_identifier(identifier: &Identifier, name: &str) {
        assert_eq!(&identifier.token, &Token::Ident(name.to_owned().clone()));
        assert_eq!(identifier.name, name);
    }

    fn test_integer_literal(expression: &Expression, value: i64) {
        let int_literal = if let Expression::IntegerLiteral(e) = expression {
            e
        } else {
            panic!("Expression is not an IntegerLiteral");
        };
        assert_eq!(int_literal.token, Token::Int(value));
        assert_eq!(int_literal.value, value);
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "5;";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");

        let expression_statement = check_expression_statement(&statements[0]);
        test_integer_literal(&expression_statement.expression, 5);
    }

    #[test]
    fn test_prefix_expression() {
        struct TestCase<'a> {
            input: &'a str,
            operator: &'a Token,
            integer_value: i64,
        }
        let tests = [
            TestCase {
                input: "!5",
                operator: &Token::Bang,
                integer_value: 5,
            },
            TestCase {
                input: "-15",
                operator: &Token::Minus,
                integer_value: 15,
            },
        ];

        for tc in tests.iter() {
            let l = Lexer::new(tc.input);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let statements = program.statements;
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression_statement = check_expression_statement(&statements[0]);
            let prefix_exp =
                if let Expression::PrefixExpression(e) = &expression_statement.expression {
                    e
                } else {
                    panic!(
                        "Expression {} is not a PrefixExpression!",
                        expression_statement.expression
                    )
                };
            assert_eq!(&prefix_exp.token, tc.operator);
            test_integer_literal(&prefix_exp.right, tc.integer_value);
        }
    }

    #[test]
    fn test_infix_expressions() {
        struct TestCase<'a> {
            input: &'a str,
            operator: &'a Token,
            left_value: i64,
            right_value: i64,
        }
        let tests = [
            TestCase {
                input: "5 + 5",
                operator: &Token::Plus,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 - 5",
                operator: &Token::Minus,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 * 5",
                operator: &Token::Asterisk,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 / 5",
                operator: &Token::Slash,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 > 5",
                operator: &Token::GT,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 < 5",
                operator: &Token::LT,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 == 5",
                operator: &Token::EQ,
                left_value: 5,
                right_value: 5,
            },
            TestCase {
                input: "5 != 5",
                operator: &Token::NotEq,
                left_value: 5,
                right_value: 5,
            },
        ];

        for tc in tests.iter() {
            let l = Lexer::new(tc.input);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let statements = program.statements;
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression_statement = check_expression_statement(&statements[0]);
            test_infix_expression(
                &expression_statement.expression,
                tc.left_value,
                tc.right_value,
                tc.operator,
            )
        }
    }

    fn test_infix_expression(
        expression: &Expression,
        left_value: i64,
        right_value: i64,
        operator: &Token,
    ) {
        let infix_exp = if let Expression::InfixExpression(e) = expression {
            e
        } else {
            panic!("Expression is not an InfixExpression");
        };
        test_integer_literal(&infix_exp.left, left_value);
        test_integer_literal(&infix_exp.right, right_value);
        assert_eq!(operator, &infix_exp.operator);
    }

    fn test_infix_expression_identifier(
        expression: &Expression,
        left_value: &str,
        right_value: &str,
        operator: &Token,
    ) {
        let infix_exp = if let Expression::InfixExpression(e) = expression {
            e
        } else {
            panic!("Expression {} is not a InfixExpression!", expression);
        };
        test_identifier_expression(&infix_exp.left, left_value);
        test_identifier_expression(&infix_exp.right, right_value);
        assert_eq!(operator, &infix_exp.operator);
    }

    #[test]
    fn test_operator_precedence_parsing() {
        let tests = [
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)\n((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("true", "true"),
            ("false", "false"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
        ];

        for tc in tests.iter() {
            let l = Lexer::new(tc.0);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let actual = program.to_string();
            assert_eq!(actual, tc.1);
        }
    }

    #[test]
    fn test_boolean_expression() {
        let tests = [("true;", true), ("false;", false)];

        for tc in tests.iter() {
            let l = Lexer::new(tc.0);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let statements = program.statements;
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression = &check_expression_statement(&statements[0]).expression;
            if let Expression::Boolean(e) = expression {
                assert_eq!(e.value, tc.1);
            } else {
                panic!("expression is not a boolean expression");
            }
        }
    }

    #[test]
    fn test_if_expression() {
        let input = "if (3 < 10) { x }";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        let if_expression = if let Expression::IfExpression(e) = &expression_statement.expression {
            e
        } else {
            panic!("Expression is not an IfExpression");
        };
        test_infix_expression(&if_expression.condition, 3, 10, &Token::LT);
        assert_eq!(if_expression.consequence.statements.len(), 1);
        let expression_statement =
            check_expression_statement(&if_expression.consequence.statements[0]);
        test_identifier_expression(&expression_statement.expression, "x");
        assert!(if_expression.alternate.is_none());
    }

    #[test]
    fn test_if_else_expression() {
        let input = "if (x < y) { x } else { y }";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        let if_expression = if let Expression::IfExpression(e) = &expression_statement.expression {
            e
        } else {
            panic!("Expression is not an IfExpression");
        };
        test_infix_expression_identifier(&if_expression.condition, "x", "y", &Token::LT);

        assert_eq!(if_expression.consequence.statements.len(), 1);
        let expression_statement =
            check_expression_statement(&if_expression.consequence.statements[0]);
        test_identifier_expression(&expression_statement.expression, "x");

        assert!(if_expression.alternate.is_some());
        let alternate_block = if_expression.alternate.as_ref().unwrap();
        assert_eq!(alternate_block.statements.len(), 1);
        let expression_statement = check_expression_statement(&alternate_block.statements[0]);
        test_identifier_expression(&expression_statement.expression, "y");
    }

    #[test]
    fn test_function_literal() {
        let input = "fn(x, y) { x + y; }";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        let function_literal =
            if let Expression::FunctionLiteral(e) = &expression_statement.expression {
                e
            } else {
                panic!("Expression is not an FunctionLiteral");
            };

        assert_eq!(2, function_literal.parameters.len());
        test_identifier(&function_literal.parameters[0], "x");
        test_identifier(&function_literal.parameters[1], "y");

        let body_statement =
            if let Statement::ExpressionStatement(s) = &function_literal.body.statements[0] {
                s
            } else {
                panic!("Statement is not an ExpressionStatement");
            };
        test_infix_expression_identifier(&body_statement.expression, "x", "y", &Token::Plus);
    }

    #[test]
    fn test_parse_parameters() {
        let tests = [
            ("fn() {};", vec![]),
            ("fn(x) {};", vec!["x"]),
            ("fn(x, y, z) {};", vec!["x", "y", "z"]),
        ];

        for tc in tests.iter() {
            let l = Lexer::new(tc.0);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let statements = program.statements;
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression_statement = check_expression_statement(&statements[0]);
            let function_literal =
                if let Expression::FunctionLiteral(e) = &expression_statement.expression {
                    e
                } else {
                    panic!("Expression is not an FunctionLiteral");
                };
            assert_eq!(function_literal.parameters.len(), tc.1.len());

            for (idx, val) in (&tc.1).into_iter().enumerate() {
                test_identifier(&function_literal.parameters[idx], val);
            }
        }
    }

    #[test]
    pub fn test_parse_call_expression() {
        let input = "add(1, 2 * 3, 4 + 5);";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = check_parse_errors(p.parse_program());
        let statements = program.statements;
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        let call_expression =
            if let Expression::CallExpression(e) = &expression_statement.expression {
                e
            } else {
                panic!("Expression is not an CallExpression");
            };
        test_identifier_expression(&call_expression.function, "add");
        assert_eq!(call_expression.arguments.len(), 3);
        test_integer_literal(&call_expression.arguments[0], 1);
        test_infix_expression(&call_expression.arguments[1], 2, 3, &Token::Asterisk);
        test_infix_expression(&call_expression.arguments[2], 4, 5, &Token::Plus);
    }

    #[test]
    fn test_function_args_parsing() {
        struct TestCase<'a> {
            input: &'a str,
            expected_args: Vec<&'a str>,
            expected_ident: &'a str,
        }

        let tests = [
            TestCase {
                input: "add();",
                expected_ident: "add",
                expected_args: vec![],
            },
            TestCase {
                input: "add(1);",
                expected_ident: "add",
                expected_args: vec!["1"],
            },
            TestCase {
                input: "add(1, 2 * 3, 4 + 5);",
                expected_ident: "add",
                expected_args: vec!["1", "(2 * 3)", "(4 + 5)"],
            },
        ];

        for tc in tests.iter() {
            let input = tc.input;
            let l = Lexer::new(input);
            let mut p = Parser::new(l);
            let program = check_parse_errors(p.parse_program());
            let statements = program.statements;
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression_statement = check_expression_statement(&statements[0]);
            let call_expression =
                if let Expression::CallExpression(e) = &expression_statement.expression {
                    e
                } else {
                    panic!(
                        "Expression {} is not a CallExpression!",
                        expression_statement.expression
                    )
                };
            test_identifier_expression(&call_expression.function, tc.expected_ident);
            assert_eq!(call_expression.arguments.len(), tc.expected_args.len());
            for (idx, arg) in tc.expected_args.iter().enumerate() {
                assert_eq!(arg, &call_expression.arguments[idx].to_string().as_str())
            }
        }
    }
}
