use std::fmt;

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
    UnaryIncorrectTypes {
        op: UnaryOperator,
        expr: ExpressionResult,
    },
    InfixIncorrectTypes {
        op: InfixOperator,
        lhs: ExpressionResult,
        rhs: ExpressionResult,
    },
    CantProcessIdentifierLiteral(String),
}

pub fn evaluate_program(program: Program) -> Result<(), EvalError> {
    for statement in program.statements {
        match statement {
            Statement::Expression(expr) => {
                evaluate_expression(expr)?;
            },
            Statement::Print(expr) => println!("{}", evaluate_expression(expr)?),
            Statement::Declaration{ identifier, expr } => println!("DECLARATION {} = {:?}", identifier, expr),
        }
    }
    Ok(())
}

pub fn evaluate_expression(expr: Expression) -> Result<ExpressionResult, EvalError> {
    match expr {
        Expression::Literal(lit) => evaluate_literal(lit),
        Expression::Unary { op, expr } => evaluate_unary(op, *expr),
        Expression::Infix { op, lhs, rhs } => evaluate_infix(op, *lhs, *rhs),
    }
}

fn evaluate_literal(lit: Literal) -> Result<ExpressionResult, EvalError> {
    match &lit {
        Literal::Number(x) => Ok(ExpressionResult::Number(*x)),
        Literal::String(x) => Ok(ExpressionResult::String(x.clone())),
        Literal::True => Ok(ExpressionResult::Bool(true)),
        Literal::False => Ok(ExpressionResult::Bool(false)),
        Literal::Nil => Ok(ExpressionResult::Nil),
        Literal::Identifier(x) => Err(EvalError::CantProcessIdentifierLiteral(x.clone())),
    }
}

fn evaluate_unary(op: UnaryOperator, expr: Expression) -> Result<ExpressionResult, EvalError> {
    let expr_result = evaluate_expression(expr)?;

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

fn evaluate_infix(op: InfixOperator, lhs: Expression, rhs: Expression) -> Result<ExpressionResult, EvalError> {
    let lhs_result = evaluate_expression(lhs)?;
    let rhs_result = evaluate_expression(rhs)?;

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
