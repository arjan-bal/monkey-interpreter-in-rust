use std::{
    collections::HashMap,
    error::Error,
    fmt::{self, Display},
};

use crate::{
    ast::{
        Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement,
        PrefixExpression, Program, ReturnStatement, Statement,
    },
    lexer::Lexer,
    token::Token,
};

type PrefixParseFn =
    Box<dyn Fn(&mut ParserInternal, &ParsingContext) -> Result<Box<dyn Expression>, ParseError>>;
type InfixParseFn = Box<
    dyn Fn(
        &mut ParserInternal,
        Box<dyn Expression>,
        &ParsingContext,
    ) -> Result<Box<dyn Expression>, ParseError>,
>;

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
}

impl ParsingContext {
    fn register_prefix(&mut self, token: &Token, func: PrefixParseFn) {
        self.prefix_parse_fns.insert(token.clone(), func);
    }

    fn register_infix(&mut self, token: &Token, func: InfixParseFn) {
        self.infix_parse_fns.insert(token.clone(), func);
    }

    fn new() -> ParsingContext {
        ParsingContext {
            prefix_parse_fns: HashMap::new(),
            infix_parse_fns: HashMap::new(),
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

enum Precedence {
    LOWEST,
    EQUALS,      // ==
    LESSGREATER, // > or <
    SUM,         // +
    PRODUCT,     // *
    PREFIX,      // -X or !X
    CALL,        // myFunction(X)
}

#[derive(Debug)]
pub struct ParseErrors(Vec<ParseError>);

impl Error for ParseErrors {}

impl Display for ParseErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
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
        let mut prefix_fns = Vec::new();
        prefix_fns.push((
            ParserInternal::parse_identifier(),
            Token::Ident(String::from("")),
        ));
        prefix_fns.push((ParserInternal::parse_integer_literal(), Token::Int(0)));
        prefix_fns.push((ParserInternal::parse_prefix_expressions(), Token::Bang));
        prefix_fns.push((ParserInternal::parse_prefix_expressions(), Token::Minus));
        while !prefix_fns.is_empty() {
            let (func, token) = prefix_fns.pop().unwrap();
            ctx.register_prefix(&token.get_representative_token(), func);
        }
        p
    }

    fn parse_identifier() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, _: &ParsingContext| {
            let ident = parser.cur_token.as_ref().unwrap().clone();
            let res: Box<dyn Expression> = Box::new(Identifier::new(ident));
            Ok(res)
        };
        Box::new(f)
    }

    fn parse_integer_literal() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, _: &ParsingContext| {
            let integer_literal = parser.cur_token.as_ref().unwrap().clone();
            let res: Box<dyn Expression> = Box::new(IntegerLiteral::new(integer_literal));
            Ok(res)
        };
        Box::new(f)
    }

    fn parse_expression(
        &mut self,
        precedence: Precedence,
        ctx: &ParsingContext,
    ) -> Result<Box<dyn Expression>, ParseError> {
        let prefix_fn = match ctx
            .prefix_parse_fns
            .get(&self.cur_token.as_ref().unwrap().get_representative_token())
        {
            Some(f) => f,
            None => {
                return Err(ParseError(format!(
                    "prefix function not found for token: {:?}",
                    self.cur_token
                )))
            }
        };
        prefix_fn(self, ctx)
    }

    fn parse_prefix_expressions() -> PrefixParseFn {
        let f = |parser: &mut ParserInternal, ctx: &ParsingContext| {
            let token = parser.cur_token.take().unwrap();
            parser.next_token();
            let right_expression = match parser.parse_expression(Precedence::PREFIX, ctx) {
                Ok(exp) => exp,
                Err(e) => return Err(e),
            };
            let res: Box<dyn Expression> = Box::new(PrefixExpression::new(token, right_expression));
            Ok(res)
        };
        Box::new(f)
    }

    fn parse_expression_statement(
        &mut self,
        ctx: &ParsingContext,
    ) -> Result<Box<dyn Statement>, ParseError> {
        let first_token = match self.cur_token.as_ref() {
            Some(t) => t.clone(),
            None => {
                return Err(ParseError(format!(
                    "Found empty cur token while parsing expression"
                )))
            }
        };
        let exp = self.parse_expression(Precedence::LOWEST, ctx)?;
        if self.peek_token == Some(Token::Semicolon) {
            self.next_token();
        }
        Ok(Box::new(ExpressionStatement::new(first_token, exp)))
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

    fn parse_statement(&mut self, ctx: &ParsingContext) -> Result<Box<dyn Statement>, ParseError> {
        match (self.cur_token.as_ref(), self.peek_token.as_ref()) {
            (Some(&Token::Let), _) => self.parse_let_statement(),
            (Some(&Token::Return), _) => self.parse_return_statement(),
            _ => self.parse_expression_statement(ctx),
        }
    }

    fn parse_program(&mut self, ctx: &ParsingContext) -> Result<Program, ParseErrors> {
        let mut prog = Program::new();
        let mut parse_errors = Vec::new();
        while self.cur_token != None && self.cur_token != Some(Token::EOF) {
            match self.parse_statement(ctx) {
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
        ast::{
            Expression, ExpressionStatement, Identifier, IntegerLiteral, LetStatement, Node,
            PrefixExpression, Program, ReturnStatement, Statement,
        },
        lexer::Lexer,
        parser::Parser,
        token::Token,
    };

    use super::ParseErrors;

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
let y = 10;
let foobar = 838383;
"#;
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements();
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
            let got_name = match let_statement.name().token().unwrap() {
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

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements();
        assert_eq!(statements.len(), 3, "program doesn't contain 3 statements");

        for statement in statements.iter() {
            assert_eq!(statement.token().unwrap(), &Token::Return);
            statement
                .as_any()
                .downcast_ref::<ReturnStatement>()
                .expect("Statement is not a ReturnStatement!");
        }
    }

    fn check_expression_statement<'a>(
        statement: &'a Box<dyn Statement + 'a>,
    ) -> &'a ExpressionStatement {
        statement
            .as_any()
            .downcast_ref::<ExpressionStatement>()
            .expect("Statement is not an ExpressionStatement!")
    }

    #[test]
    fn test_identifier_expression() {
        let input = "foobar;";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements();
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
        let expression_statement = check_expression_statement(&statements[0]);
        let expression = expression_statement
            .expression()
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("expression is not an identifier");
        assert_eq!(
            expression.token().unwrap(),
            &Token::Ident("foobar".to_owned())
        );
        assert_eq!(expression.value(), "foobar");
    }

    fn test_integer_literal(expression: &Box<dyn Expression>, value: i64) {
        let int_literal = expression
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expression is not an IntegerLiteral");
        assert_eq!(int_literal.token().unwrap(), &Token::Int(value));
        assert_eq!(int_literal.value(), value);
    }

    #[test]
    fn test_integer_literal_expression() {
        let input = "5;";
        let l = Lexer::new(input);
        let mut p = Parser::new(l);

        let program = check_parse_errors(p.parse_program());
        let statements = program.statements();
        assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");

        let expression_statement = check_expression_statement(&statements[0]);
        test_integer_literal(expression_statement.expression(), 5);
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
            let statements = program.statements();
            assert_eq!(statements.len(), 1, "program doesn't contain 1 statement");
            let expression_statement = check_expression_statement(&statements[0]);
            let prefix_exp = expression_statement
                .expression()
                .as_any()
                .downcast_ref::<PrefixExpression>()
                .expect("expression is not a prefix expression");
            assert_eq!(prefix_exp.token().unwrap(), tc.operator);
            test_integer_literal(prefix_exp.right(), tc.integer_value);
        }
    }
}
