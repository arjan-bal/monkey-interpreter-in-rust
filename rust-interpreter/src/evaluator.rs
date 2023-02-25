use crate::{
    ast::{Expression, IfExpression, Node, PrefixExpression, Statement},
    object::Object,
    token::Token,
};

pub fn eval(node: &Node) -> Object {
    match node {
        Node::Expression(e) => eval_expression(e),
        Node::Statement(s) => eval_statement(s),
        Node::Program(p) => eval_statements(&p.statements),
        Node::BlockStatement(b) => eval_statements(&b.statements),
    }
}

fn eval_expression(expression: &Expression) -> Object {
    match expression {
        Expression::IntegerLiteral(x) => Object::Integer(x.value),
        Expression::Identifier(_) => todo!(),
        Expression::Boolean(b) => Object::Boolean(b.value),
        Expression::CallExpression(_) => todo!(),
        Expression::IfExpression(e) => eval_if_expression(e),
        Expression::FunctionLiteral(_) => todo!(),
        Expression::InfixExpression(e) => {
            let left = eval_expression(&e.left);
            let right = eval_expression(&e.right);
            eval_infix_expression(&left, &right, &e.operator)
        }
        Expression::PrefixExpression(e) => eval_prefix_expression(e),
    }
}

fn eval_if_expression(expression: &IfExpression) -> Object {
    let condition = eval_expression(&expression.condition);
    if is_truthy(&condition) {
        return eval_statements(&expression.consequence.statements);
    }
    match &expression.alternate {
        Some(s) => eval_statements(&s.statements),
        None => Object::Null(),
    }
}

fn is_truthy(object: &Object) -> bool {
    match object {
        Object::Boolean(b) => *b,
        Object::Null() => false,
        _ => true,
    }
}

fn eval_prefix_expression(e: &PrefixExpression) -> Object {
    match e.token {
        Token::Bang => eval_bang_operator_expression(&e.right),
        Token::Minus => eval_minus_expression(&e.right),
        _ => todo!(),
    }
}

fn eval_infix_expression(left: &Object, right: &Object, operator: &Token) -> Object {
    match (left, right) {
        (&Object::Integer(l), &Object::Integer(r)) => match operator {
            &Token::Plus => Object::Integer(l + r),
            &Token::Minus => Object::Integer(l - r),
            &Token::Asterisk => Object::Integer(l * r),
            &Token::Slash => Object::Integer(l / r),
            &Token::LT => Object::Boolean(l < r),
            &Token::GT => Object::Boolean(l > r),
            &Token::EQ => Object::Boolean(l == r),
            &Token::NotEq => Object::Boolean(l != r),
            _ => panic!("Operator {} not supported for integers", operator),
        },
        (&Object::Boolean(l), &Object::Boolean(r)) => match operator {
            &Token::EQ => Object::Boolean(l == r),
            &Token::NotEq => Object::Boolean(l != r),
            _ => panic!("Operator {} not supported for booleans", operator),
        },
        _ => todo!(),
    }
}

fn eval_bang_operator_expression(e: &Expression) -> Object {
    let res = eval_expression(e);
    let b = match res {
        Object::Integer(_) => false,
        Object::Boolean(true) => false,
        Object::Boolean(false) => true,
        Object::Null() => true,
    };
    Object::Boolean(b)
}

fn eval_minus_expression(e: &Expression) -> Object {
    let res = eval_expression(e);
    match res {
        Object::Integer(x) => Object::Integer(-x),
        _ => panic!("Can't apply - to non integer value {}", res.inspect()),
    }
}

fn eval_statement(statement: &Statement) -> Object {
    match statement {
        Statement::LetStatement(_) => todo!(),
        Statement::ReturnStatement(_) => todo!(),
        Statement::ExpressionStatement(e) => eval_expression(&e.expression),
    }
}

fn eval_statements(statements: &Vec<Statement>) -> Object {
    let mut result = Object::Null();
    for statement in statements.iter() {
        result = eval_statement(statement);
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::{ast::Node, lexer::Lexer, object::Object, parser::Parser};

    use super::eval;

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
            let o = test_eval(tc.0);
            let res = match o {
                Object::Integer(x) => x,
                _ => panic!("Result {} is not an integer", o.inspect()),
            };
            assert_eq!(tc.1, res);
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
            let o = test_eval(tc.0);
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
            let o = test_eval(tc.0);
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
            let o = test_eval(tc.0);
            assert_eq!(tc.1, o);
        }
    }

    fn test_eval(input: &str) -> Object {
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = p.parse_program().unwrap();
        eval(&Node::Program(program))
    }
}
