use std::collections::HashMap;
use std::fmt;
use std::io::Write;

use crate::parser::{Expression, InfixOperator, Literal, Program, Statement, UnaryOperator};

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
    scopes: Vec<HashMap<String, ExpressionResult>>,
}

impl Environment {
    fn new() -> Self {
        Environment {
            scopes: vec![HashMap::new()],
        }
    }

    fn current_scope(&mut self) -> &mut HashMap<String, ExpressionResult> {
        self.scopes
            .last_mut()
            .expect("internal Environment error: no current scope!")
    }

    fn add_scope(&mut self) {
        self.scopes.push(HashMap::new())
    }

    fn pop_scope(&mut self) {
        self.scopes
            .pop()
            .expect("internal Environment error: popped too many scopes! None left");
    }

    fn define(&mut self, identifier: String, value: Option<ExpressionResult>) {
        self.current_scope()
            .insert(identifier, value.unwrap_or(ExpressionResult::Nil));
    }

    fn identifier_value(&self, identifier: &str) -> Result<ExpressionResult, EvalError> {
        // Check scopes starting with innermost scope
        for scope in self.scopes.iter().rev() {
            if let Some(val) = scope.get(identifier) {
                return Ok(val.clone());
            }
        }

        Err(EvalError::UnknownIdentifer(identifier.to_string()))
    }

    fn assign(&mut self, identifier: &str, value: ExpressionResult) -> Result<(), EvalError> {
        // Check scopes starting with innermost scope
        for scope in self.scopes.iter_mut().rev() {
            if scope.get(identifier).is_some() {
                scope.insert(identifier.to_string(), value);
                return Ok(());
            }
        }
        Err(EvalError::UnknownIdentifer(identifier.to_string()))
    }
}

pub fn evaluate_program<W: Write>(program: Program, out: &mut W) -> Result<(), EvalError> {
    let mut env = Environment::new();
    evaluate_statements(&program.statements, out, &mut env)
}

fn evaluate_statements<W: Write>(
    statements: &Vec<Statement>,
    out: &mut W,
    env: &mut Environment,
) -> Result<(), EvalError> {
    for statement in statements.iter() {
        evaluate_statement(statement, out, env)?;
    }
    Ok(())
}

fn evaluate_statement<W: Write>(
    statement: &Statement,
    out: &mut W,
    env: &mut Environment,
) -> Result<(), EvalError> {
    match statement {
        Statement::Expression(expr) => {
            evaluate_expression(&expr, env)?;
        }
        Statement::Print(expr) => {
            writeln!(out, "{}", evaluate_expression(&expr, env)?)
                .map_err(|err| EvalError::IOError(err.to_string()))?;
        }
        Statement::Declaration { identifier, expr } => {
            let result = expr
                .as_ref()
                .map(|expr| evaluate_expression(&expr, env))
                .transpose()?;
            env.define(identifier.to_string(), result);
        }
        Statement::If { condition, then_branch, else_branch } => {
            let condition_result = evaluate_expression(&condition, env)?;
            let result = result_truthiness(&condition_result);
            match (result, else_branch) {
                (true, _) => evaluate_statement(&then_branch, out, env)?,
                (false, Some(else_branch)) => evaluate_statement(&else_branch, out, env)?,
                _ => {},
            }
        }
        Statement::While{ .. } => todo!(),
        Statement::Block(stmts) => {
            env.add_scope();
            let ret = evaluate_statements(stmts, out, env);
            env.pop_scope();
            ret?
        }
    }
    Ok(())
}

fn evaluate_expression(
    expr: &Expression,
    env: &mut Environment,
) -> Result<ExpressionResult, EvalError> {
    match expr {
        Expression::Parens(expr) => evaluate_expression(expr, env),
        Expression::Assignment { target, expr } => {
            let val = evaluate_expression(expr, env)?;
            env.assign(&target, val.clone())?;
            Ok(val)
        }
        Expression::Literal(lit) => evaluate_literal(lit, env),
        Expression::Unary { op, expr } => evaluate_unary(op, expr, env),
        Expression::Infix { op, lhs, rhs } => evaluate_infix(op, lhs, rhs, env),
    }
}

fn evaluate_literal(lit: &Literal, env: &Environment) -> Result<ExpressionResult, EvalError> {
    match &lit {
        Literal::Number(x) => Ok(ExpressionResult::Number(*x)),
        Literal::String(x) => Ok(ExpressionResult::String(x.clone())),
        Literal::True => Ok(ExpressionResult::Bool(true)),
        Literal::False => Ok(ExpressionResult::Bool(false)),
        Literal::Nil => Ok(ExpressionResult::Nil),
        Literal::Identifier(x) => env.identifier_value(x),
    }
}

fn evaluate_unary(
    op: &UnaryOperator,
    expr: &Expression,
    env: &mut Environment,
) -> Result<ExpressionResult, EvalError> {
    let expr_result = evaluate_expression(expr, env)?;

    let incorrect_type_error = Err(EvalError::UnaryIncorrectTypes {
        op: op.clone(),
        expr: expr_result.clone(),
    });

    match op {
        // Lox
        UnaryOperator::Not => Ok(ExpressionResult::Bool(!result_truthiness(&expr_result))),
        UnaryOperator::Negate => match &expr_result {
            ExpressionResult::Number(x) => Ok(ExpressionResult::Number(-x)),
            _ => incorrect_type_error,
        },
    }
}

fn result_truthiness(result: &ExpressionResult) -> bool {
    match result {
        ExpressionResult::Nil => false,
        ExpressionResult::Bool(x) => x.clone(),
        _ => true,
    }
}

fn evaluate_infix(
    op: &InfixOperator,
    lhs: &Expression,
    rhs: &Expression,
    env: &mut Environment,
) -> Result<ExpressionResult, EvalError> {
    match op {
        InfixOperator::Equals => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) =>
            {
                #[allow(clippy::float_cmp)]
                Ok(ExpressionResult::Bool(x == y))
            }
            (ExpressionResult::String(x), ExpressionResult::String(y)) => {
                Ok(ExpressionResult::Bool(x == y))
            }
            (ExpressionResult::Bool(x), ExpressionResult::Bool(y)) => {
                Ok(ExpressionResult::Bool(x == y))
            }
            (ExpressionResult::Nil, ExpressionResult::Nil) => Ok(ExpressionResult::Bool(true)),
            (lhs_result, rhs_result) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_result,
                rhs: rhs_result,
            }),
        },
        InfixOperator::NotEquals => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) =>
            {
                #[allow(clippy::float_cmp)]
                Ok(ExpressionResult::Bool(x != y))
            }
            (ExpressionResult::String(x), ExpressionResult::String(y)) => {
                Ok(ExpressionResult::Bool(x != y))
            }
            (ExpressionResult::Bool(x), ExpressionResult::Bool(y)) => {
                Ok(ExpressionResult::Bool(x != y))
            }
            (ExpressionResult::Nil, ExpressionResult::Nil) => Ok(ExpressionResult::Bool(false)),
            (lhs_result, rhs_result) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_result,
                rhs: rhs_result,
            }),
        },
        InfixOperator::Less => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Bool(x < y)
        }),
        InfixOperator::LessEqual => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Bool(x <= y)
        }),
        InfixOperator::Greater => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Bool(x > y)
        }),
        InfixOperator::GreaterEqual => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Bool(x >= y)
        }),
        InfixOperator::Plus => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (ExpressionResult::Number(x), ExpressionResult::Number(y)) => {
                Ok(ExpressionResult::Number(x + y))
            }
            (ExpressionResult::String(x), ExpressionResult::String(y)) => {
                Ok(ExpressionResult::String(x + &y.to_string()))
            }
            (lhs_result, rhs_result) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_result,
                rhs: rhs_result,
            }),
        },
        InfixOperator::Minus => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Number(x - y)
        }),
        InfixOperator::Times => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Number(x * y)
        }),
        InfixOperator::Divide => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            ExpressionResult::Number(x / y)
        }),
        InfixOperator::Or => {
            let lhs_result = evaluate_expression(lhs, env)?;
            if result_truthiness(&lhs_result) {
                Ok(lhs_result)
            } else {
                evaluate_expression(rhs, env)
            }
        }
        InfixOperator::And => {
            let lhs_result = evaluate_expression(lhs, env)?;
            if !result_truthiness(&lhs_result) {
                Ok(lhs_result)
            } else {
                evaluate_expression(rhs, env)
            }
        }
    }
}

fn evaluate_numeric_infix(
    op: &InfixOperator,
    lhs: &Expression,
    rhs: &Expression,
    env: &mut Environment,
    f: fn (f64, f64) -> ExpressionResult
) -> Result<ExpressionResult, EvalError> {
    let lhs_result = evaluate_expression(lhs, env)?;
    let rhs_result = evaluate_expression(rhs, env)?;

    match (&lhs_result, &rhs_result) {
        (ExpressionResult::Number(x), ExpressionResult::Number(y)) => {
            Ok(f(*x, *y))
        }
        _ => Err(EvalError::InfixIncorrectTypes {
            op: op.clone(),
            lhs: lhs_result.clone(),
            rhs: rhs_result.clone(),
        }),
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
            "#,
            "5\n6\n",
        );

        assert_success_output(
            r#"
              var x = 4;
              print !(x - 4 == 0);
            "#,
            "false\n",
        );

        assert_success_output("if (1 == 2) print 100; else print 200;", "200\n");
        assert_success_output("if (1 == 1) print 100;", "100\n");
        assert_success_output("if (1 == 2) print 100;", "");

        // Ensure assignment works
        assert_success_output(
            r#"
              var x = 3;
              x = 4;
              print x;
            "#,
            "4\n",
        );

        // Assignment has a side effect and also returns a value
        assert_success_output(
            r#"
              var x;
              print x;
              print x = 4;
              print x;
            "#,
            "nil\n4\n4\n",
        );

        // Complex nested scopes
        assert_success_output(
            r#"
              var a = "global a";
              var b = "global b";
              var c = "global c";
              {
                var a = "outer a";
                var b = "outer b";
                {
                  var a = "inner a";
                  print a;
                  print b;
                  print c;
                }
                print a;
                print b;
                print c;
              }
              print a;
              print b;
              print c;
            "#,
            r#""inner a"
"outer b"
"global c"
"outer a"
"outer b"
"global c"
"global a"
"global b"
"global c"
"#,
        );

        // Var shadows in a block, but assignment overwrites
        assert_success_output(
            r#"
              var a = 1;
              var b = 1;
              {
                var a = 2;
                b = 2;
                print a;
                print b;
              }
              print a;
              print b;
            "#,
            "2\n2\n1\n2\n",
        );

        // Logical operators: or
        assert_success_output("print nil or 1;", "1\n");
        assert_success_output("print 2 or 3;", "2\n");

        // Logical operators: or short circuits
        assert_success_output("var x = 10; true or (x = 20); print x;", "10\n");
        assert_success_output("var x = 10; false or (x = 20); print x;", "20\n");

        // Logical operators: and
        assert_success_output("print 1 and 2;", "2\n");
        assert_success_output("print false and 2;", "false\n");

        // Logical operators: and short circuits
        assert_success_output("var x = 10; false and (x = 20); print x;", "10\n");
        assert_success_output("var x = 10; true and (x = 20); print x;", "20\n");

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
