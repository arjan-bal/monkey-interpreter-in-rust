use crate::{
    ast::{Expression, Node, Program, Statement},
    object::Object,
};

pub fn eval(node: &Node) -> Object {
    match node {
        Node::Expression(e) => eval_expression(e),
        Node::Statement(s) => eval_statement(s),
        Node::Program(p) => eval_program(p),
    }
}

fn eval_expression(expression: &Expression) -> Object {
    match expression {
        Expression::IntegerLiteral(x) => Object::Integer(x.value),
        _ => panic!("Eval not implemented for {}", expression),
    }
}

fn eval_statement(statement: &Statement) -> Object {
    match statement {
        Statement::LetStatement(_) => todo!(),
        Statement::ReturnStatement(_) => todo!(),
        Statement::ExpressionStatement(e) => eval_expression(&e.expression),
    }
}

fn eval_program(program: &Program) -> Object {
    let mut result = Object::Null();
    for statement in program.statements.iter() {
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
        let tests = [("5", 5), ("10", 10)];

        for tc in tests.iter() {
            let o = test_eval(tc.0);
            let res = match o {
                Object::Integer(x) => x,
                _ => panic!("Result {} is not an integer", o.inspect()),
            };
            assert_eq!(tc.1, res);
        }
    }

    fn test_eval(input: &str) -> Object {
        let l = Lexer::new(input);
        let mut p = Parser::new(l);
        let program = p.parse_program().unwrap();
        eval(&Node::Program(program))
    }
}
