use std::collections::HashMap;
use std::fmt;
use std::io::Write;

use crate::parser::{Expression, InfixOperator, UnaryOperator, Literal, Program, Statement};

#[derive(Debug, PartialEq, Clone)]
pub enum ExpressionResult {
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

impl fmt::Display for ExpressionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionResult::Number(x) => write!(f, "{}", x),
            ExpressionResult::String(x) => write!(f, "\"{}\"", x),
            ExpressionResult::Bool(x) => write!(f, "{}", x),
            ExpressionResult::Nil => write!(f, "nil"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum EvalError {
    IOError(String),
    UnaryIncorrectTypes {
        op: UnaryOperator,
        expr: ExpressionResult,
    },
    InfixIncorrectTypes {
        op: InfixOperator,
        lhs: ExpressionResult,
        rhs: ExpressionResult,
    },
    UnknownIdentifer(String),
}

struct Environment {
    identifiers: HashMap<String, ExpressionResult>,
}

impl Environment {
    fn new() -> Self {
        Environment {
            identifiers: HashMap::new(),
        }
    }

    fn define(&mut self, identifier: String, value: Option<ExpressionResult>) {
        self.identifiers.insert(identifier, value.unwrap_or(ExpressionResult::Nil));
    }

    fn identifier_value(&self, identifier: &String) -> Result<ExpressionResult, EvalError> {
        match self.identifiers.get(identifier) {
            Some(val) => Ok(val.clone()),
            None => Err(EvalError::UnknownIdentifer(identifier.clone())),
        }
    }

    fn assign(&mut self, identifier: &String, value: ExpressionResult) -> Result<(), EvalError> {
        match self.identifiers.get(identifier) {
            Some(_) => {
                self.identifiers.insert(identifier.clone(), value);
                Ok(())
            }
            None => Err(EvalError::UnknownIdentifer(identifier.clone())),
        }
    }

}

pub fn evaluate_program<W: Write>(program: Program, out: &mut W) -> Result<(), EvalError> {
    let mut env = Environment::new();
    for statement in program.statements {
        match statement {
            Statement::Expression(expr) => {
                evaluate_expression(expr, &mut env)?;
            },
            Statement::Print(expr) => {
                writeln!(out, "{}", evaluate_expression(expr, &mut env)?)
                    .map_err(|err| EvalError::IOError(err.to_string()))?;
            }
            Statement::Declaration{ identifier, expr } => {
                let result = expr.map(|expr| evaluate_expression(expr, &mut env)).transpose()?;
                env.define(identifier, result);
            },
        }
    }
    Ok(())
}

fn evaluate_expression(expr: Expression, env: &mut Environment) -> Result<ExpressionResult, EvalError> {
    match expr {
        Expression::Assignment { target, expr } => {
            let val = evaluate_expression(*expr, env)?;
            env.assign(&target, val.clone())?;
            Ok(val)
        },
        Expression::Literal(lit) => evaluate_literal(lit, env),
        Expression::Unary { op, expr } => evaluate_unary(op, *expr, env),
        Expression::Infix { op, lhs, rhs } => evaluate_infix(op, *lhs, *rhs, env),
    }
}

fn evaluate_literal(lit: Literal, env: &Environment) -> Result<ExpressionResult, EvalError> {
    match &lit {
        Literal::Number(x) => Ok(ExpressionResult::Number(*x)),
        Literal::String(x) => Ok(ExpressionResult::String(x.clone())),
        Literal::True => Ok(ExpressionResult::Bool(true)),
        Literal::False => Ok(ExpressionResult::Bool(false)),
        Literal::Nil => Ok(ExpressionResult::Nil),
        Literal::Identifier(x) => env.identifier_value(x),
    }
}

fn evaluate_unary(op: UnaryOperator, expr: Expression, env: &mut Environment) -> Result<ExpressionResult, EvalError> {
    let expr_result = evaluate_expression(expr, env)?;

    let incorrect_type_error = Err(EvalError::UnaryIncorrectTypes{
        op: op.clone(),
        expr: expr_result.clone(),
    });

    match op {
        // Lox
        UnaryOperator::Not => match &expr_result {
            ExpressionResult::Nil => Ok(ExpressionResult::Bool(true)),
            ExpressionResult::Bool(x) => Ok(ExpressionResult::Bool(!x)),
            _ => Ok(ExpressionResult::Bool(true)),
        },
        UnaryOperator::Negate => match &expr_result {
            ExpressionResult::Number(x) => Ok(ExpressionResult::Number(-x)),
            _ => incorrect_type_error,
        },
    }

}

fn evaluate_infix(op: InfixOperator, lhs: Expression, rhs: Expression, env: &mut Environment) -> Result<ExpressionResult, EvalError> {
    let lhs_result = evaluate_expression(lhs, env)?;
    let rhs_result = evaluate_expression(rhs, env)?;

    let incorrect_type_error = Err(EvalError::InfixIncorrectTypes{
        op: op.clone(),
        lhs: lhs_result.clone(),
        rhs: rhs_result.clone()
    });

    match op {
        InfixOperator::Equals => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => {
                #[allow(clippy::float_cmp)]
                Ok(ExpressionResult::Bool(x == y))
            },
            (ExpressionResult::String(x), ExpressionResult::String(y)) => Ok(ExpressionResult::Bool(x == y)),
            (ExpressionResult::Bool(x), ExpressionResult::Bool(y)) => Ok(ExpressionResult::Bool(x == y)),
            (ExpressionResult::Nil, ExpressionResult::Nil) => Ok(ExpressionResult::Bool(true)),
            _ => incorrect_type_error,
        }
        InfixOperator::NotEquals => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => {
                #[allow(clippy::float_cmp)]
                Ok(ExpressionResult::Bool(x != y))
            },
            (ExpressionResult::String(x), ExpressionResult::String(y)) => Ok(ExpressionResult::Bool(x != y)),
            (ExpressionResult::Bool(x), ExpressionResult::Bool(y)) => Ok(ExpressionResult::Bool(x != y)),
            (ExpressionResult::Nil, ExpressionResult::Nil) => Ok(ExpressionResult::Bool(false)),
            _ => incorrect_type_error,
        }
        InfixOperator::Less => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Bool(x < y)),
            _ => incorrect_type_error,
        }
        InfixOperator::LessEqual => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Bool(x <= y)),
            _ => incorrect_type_error,
        }
        InfixOperator::Greater => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Bool(x > y)),
            _ => incorrect_type_error,
        }
        InfixOperator::GreaterEqual => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Bool(x >= y)),
            _ => incorrect_type_error,
        }
        InfixOperator::Plus => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Number(x + y)),
            (ExpressionResult::String(x), ExpressionResult::String(y)) => Ok(ExpressionResult::String(x.clone() + y)),
            _ => incorrect_type_error,
        }
        InfixOperator::Minus => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Number(x - y)),
            _ => incorrect_type_error,
        }
        InfixOperator::Times => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Number(x * y)),
            _ => incorrect_type_error,
        }
        InfixOperator::Divide => match (&lhs_result, &rhs_result) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => Ok(ExpressionResult::Number(x / y)),
            _ => incorrect_type_error,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    #[test]
    fn test_evaluate_program() {
        fn assert_success_output(input: &str, expected_output: &str) {
            let mut lexer = Lexer::new(input);
            lexer.lex().expect("lexing failed");
            let program = Parser::new(lexer.tokens).parse().expect("parse error");
            let mut buf = Vec::new();
            assert_eq!(evaluate_program(program, &mut buf), Ok(()));
            assert_eq!(String::from_utf8(buf), Ok(expected_output.to_string()));
        }

        assert_success_output(
            r#"
              var x = 2 + 3;
              print x;
              print x + 1;
            "#, "5\n6\n");

        assert_success_output(
            r#"
              var x = 4;
              print !(x - 4 == 0);
            "#, "false\n");

        // Ensure assignment works
        assert_success_output(
            r#"
              var x = 3;
              x = 4;
              print x;
            "#, "4\n");

        // Assignment has a side effect and also returns a value
        assert_success_output(
            r#"
              var x;
              print x;
              print x = 4;
              print x;
            "#, "nil\n4\n4\n");

        fn assert_failure_output(input: &str, expected: EvalError) {
            let mut lexer = Lexer::new(input);
            lexer.lex().expect("lexing failed");
            let program = Parser::new(lexer.tokens).parse().expect("parse error");
            let mut buf = Vec::new();
            assert_eq!(evaluate_program(program, &mut buf), Err(expected));
        }

        // Try to print nonexistent variable
        assert_failure_output("print x;", EvalError::UnknownIdentifer("x".to_string()));

        // Assign to nonexistent variable
        assert_failure_output("x = 4;", EvalError::UnknownIdentifer("x".to_string()));
    }
}
