use crate::{
    ast::{Expression, IfExpression, Node, PrefixExpression, Statement},
    object::{Environment, Object},
    token::Token,
};
use std::fmt::Display;
use std::{error::Error, fmt};

#[derive(Debug)]
pub struct EvalError(String);

impl Error for EvalError {}

impl Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

type EvalResult = Result<Object, EvalError>;

pub fn eval(node: &Node, env: &mut Environment) -> EvalResult {
    match node {
        Node::Expression(e) => eval_expression(e, env),
        Node::Statement(s) => eval_statement(s, env),
        Node::Program(p) => eval_statements(&p.statements, true, env),
        Node::BlockStatement(b) => eval_statements(&b.statements, false, env),
    }
}

fn eval_expression(expression: &Expression, env: &mut Environment) -> EvalResult {
    match expression {
        Expression::IntegerLiteral(x) => Ok(Object::Integer(x.value)),
        Expression::Identifier(i) => match env.get(&i.name) {
            Some(o) => Ok(o.clone()),
            None => Err(EvalError(format!("identifier not found: {}", &i.name))),
        },
        Expression::Boolean(b) => Ok(Object::Boolean(b.value)),
        Expression::CallExpression(_) => todo!(),
        Expression::IfExpression(e) => eval_if_expression(e, env),
        Expression::FunctionLiteral(_) => todo!(),
        Expression::InfixExpression(e) => {
            let left = eval_expression(&e.left, env)?;
            let right = eval_expression(&e.right, env)?;
            eval_infix_expression(&left, &right, &e.operator, env)
        }
        Expression::PrefixExpression(e) => eval_prefix_expression(e, env),
    }
}

fn eval_if_expression(expression: &IfExpression, env: &mut Environment) -> EvalResult {
    let condition = eval_expression(&expression.condition, env)?;
    if is_truthy(&condition) {
        return eval_statements(&expression.consequence.statements, false, env);
    }
    match &expression.alternate {
        Some(s) => eval_statements(&s.statements, false, env),
        None => Ok(Object::Null()),
    }
}

fn is_truthy(object: &Object) -> bool {
    match object {
        Object::Boolean(b) => *b,
        Object::Null() => false,
        _ => true,
    }
}

fn eval_prefix_expression(e: &PrefixExpression, env: &mut Environment) -> EvalResult {
    let right = eval_expression(&e.right, env)?;
    match (&e.token, &right) {
        (Token::Bang, _) => Ok(eval_bang_operator_expression(right)),
        (Token::Minus, Object::Integer(i)) => Ok(eval_minus_expression(*i)),
        _ => Err(EvalError(format!(
            "unknown operator: {}{}",
            e.token,
            right.type_name()
        ))),
    }
}

fn eval_infix_expression(
    left: &Object,
    right: &Object,
    operator: &Token,
    env: &mut Environment,
) -> EvalResult {
    if left.type_name() != right.type_name() {
        return Err(EvalError(format!(
            "type mismatch: {} {} {}",
            left.type_name(),
            operator,
            right.type_name()
        )));
    }
    let res = match (left, right) {
        (&Object::Integer(l), &Object::Integer(r)) => match operator {
            &Token::Plus => Object::Integer(l + r),
            &Token::Minus => Object::Integer(l - r),
            &Token::Asterisk => Object::Integer(l * r),
            &Token::Slash => Object::Integer(l / r),
            &Token::LT => Object::Boolean(l < r),
            &Token::GT => Object::Boolean(l > r),
            &Token::EQ => Object::Boolean(l == r),
            &Token::NotEq => Object::Boolean(l != r),
            _ => {
                return Err(EvalError(format!(
                    "unknown operator: {} {} {}",
                    left.type_name(),
                    operator,
                    right.type_name(),
                )))
            }
        },
        (&Object::Boolean(l), &Object::Boolean(r)) => match operator {
            &Token::EQ => Object::Boolean(l == r),
            &Token::NotEq => Object::Boolean(l != r),
            _ => {
                return Err(EvalError(format!(
                    "unknown operator: {} {} {}",
                    left.type_name(),
                    operator,
                    right.type_name(),
                )))
            }
        },
        _ => {
            return Err(EvalError(format!(
                "unknown operator: {} {} {}",
                left.type_name(),
                operator,
                right.type_name(),
            )))
        }
    };
    Ok(res)
}

fn eval_bang_operator_expression(res: Object) -> Object {
    let b = match res {
        Object::Integer(_) => false,
        Object::Boolean(true) => false,
        Object::Boolean(false) => true,
        Object::Null() => true,
        Object::Return(_) => return res,
    };
    Object::Boolean(b)
}

fn eval_minus_expression(res: i64) -> Object {
    Object::Integer(-res)
}

fn eval_statement(statement: &Statement, env: &mut Environment) -> EvalResult {
    Ok(match statement {
        Statement::LetStatement(l) => {
            let res = eval_expression(&l.value, env)?;
            env.set(&l.name.name, res.clone());
            res
        }
        Statement::ExpressionStatement(e) => eval_expression(&e.expression, env)?,
        Statement::ReturnStatement(s) => {
            Object::Return(Box::new(eval_expression(&s.return_value, env)?))
        }
    })
}

fn eval_statements(
    statements: &Vec<Statement>,
    is_outermost: bool,
    env: &mut Environment,
) -> EvalResult {
    let mut result = Object::Null();
    for statement in statements.iter() {
        result = eval_statement(statement, env)?;
        if result.is_return() {
            return Ok(if is_outermost {
                result.get_return().unwrap()
            } else {
                result
            });
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::Node,
        lexer::Lexer,
        object::{Environment, Object},
        parser::Parser,
    };

    use super::{eval, EvalResult};

    #[test]
    fn test_evaluate_int_expression() {
        let tests = [
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for tc in tests.iter() {
            let res = test_eval(tc.0).unwrap();
            assert_eq!(Object::Integer(tc.1), res);
        }
    }

    #[test]
    fn test_evaluate_bool_expressions() {
        let tests = [
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

        for tc in tests.iter() {
            let o = test_eval(tc.0).unwrap();
            let res = match o {
                Object::Boolean(x) => x,
                _ => panic!("Result {} is not an bool", o.inspect()),
            };
            assert_eq!(tc.1, res);
        }
    }

    #[test]
    fn test_bang_operator() {
        let tests = [
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];

        for tc in tests.iter() {
            let o = test_eval(tc.0).unwrap();
            let res = match o {
                Object::Boolean(x) => x,
                _ => panic!("Result {} is not an bool", o.inspect()),
            };
            assert_eq!(tc.1, res);
        }
    }

    #[test]
    fn test_if_else_expression() {
        let tests = [
            ("if (true) { 10 }", Object::Integer(10)),
            ("if (false) { 10 }", Object::Null()),
            ("if (1) { 10 }", Object::Integer(10)),
            ("if (1 < 2) { 10 }", Object::Integer(10)),
            ("if (1 > 2) { 10 }", Object::Null()),
            ("if (1 > 2) { 10 } else { 20 }", Object::Integer(20)),
            ("if (1 < 2) { 10 } else { 20 }", Object::Integer(10)),
        ];

        for tc in tests.iter() {
            let o = test_eval(tc.0).unwrap();
            assert_eq!(tc.1, o);
        }
    }

    #[test]
    fn test_return_statement() {
        let tests = [
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            ("if (10 > 1) { if (10 > 1) { return 10; } return 1; }", 10),
        ];
        for tc in tests.iter() {
            let res = test_eval(tc.0).unwrap();
            assert_eq!(res, Object::Integer(tc.1));
        }
    }

    #[test]
    fn test_error_handling() {
        let tests = [
            ("5 + true;", "type mismatch: INTEGER + BOOLEAN"),
            ("5 + true; 5;", "type mismatch: INTEGER + BOOLEAN"),
            ("-true", "unknown operator: -BOOLEAN"),
            ("true + false;", "unknown operator: BOOLEAN + BOOLEAN"),
            ("5; true + false; 5", "unknown operator: BOOLEAN + BOOLEAN"),
            (
                "if (10 > 1){ true + false; }",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            (
                "
132
if (10 > 1){
if (10 > 1){
return true + false;
}
return 1;
}
",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            ("foobar", "identifier not found: foobar"),
        ];

        for tc in tests.iter() {
            let res = test_eval(tc.0);
            assert_eq!(res.err().unwrap().0, tc.1);
        }
    }

    #[test]
    fn test_let_statements() {
        let tests = [
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for tc in tests.iter() {
            let res = test_eval(tc.0).unwrap();
            assert_eq!(res, Object::Integer(tc.1));
        }
    }

    fn test_eval(input: &str) -> EvalResult {
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = p.parse_program().unwrap();
        eval(&Node::Program(program), &mut Environment::new())
    }
}
