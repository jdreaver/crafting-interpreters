use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::parser::{Expression, InfixOperator, Literal, Program, Statement, UnaryOperator};

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Function {
        name: String,
        arity: usize,
        body: FunctionBody,
    },
    Nil,
}

#[derive(Debug, PartialEq, Clone)]
pub enum FunctionBody {
    PrimitiveFunction(fn (Vec<Value>) -> Result<Value, EvalError>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Number(x) => write!(f, "{}", x),
            Value::String(x) => write!(f, "\"{}\"", x),
            Value::Bool(x) => write!(f, "{}", x),
            Value::Function{ name, .. } => write!(f, "<fn {}>", name),
            Value::Nil => write!(f, "nil"),
        }
    }
}

fn value_truthiness(val: &Value) -> bool {
    match val {
        Value::Nil => false,
        Value::Bool(x) => x.clone(),
        _ => true,
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum EvalError {
    IOError(String),
    UnaryIncorrectTypes {
        op: UnaryOperator,
        expr: Value,
    },
    InfixIncorrectTypes {
        op: InfixOperator,
        lhs: Value,
        rhs: Value,
    },
    UnknownIdentifer(String),
    ExpectedFunctionGot(Value),
    IncorrectArity {
        name: String,
        arity: usize,
        got: usize,
    }
}

struct Environment {
    scopes: Vec<HashMap<String, Value>>,
}

impl Environment {
    fn new() -> Self {
        Environment {
            scopes: vec![HashMap::new()],
        }
    }

    fn current_scope(&mut self) -> &mut HashMap<String, Value> {
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

    fn define(&mut self, identifier: String, value: Option<Value>) {
        self.current_scope()
            .insert(identifier, value.unwrap_or(Value::Nil));
    }

    fn identifier_value(&self, identifier: &str) -> Result<Value, EvalError> {
        // Check scopes starting with innermost scope
        for scope in self.scopes.iter().rev() {
            if let Some(val) = scope.get(identifier) {
                return Ok(val.clone());
            }
        }

        Err(EvalError::UnknownIdentifer(identifier.to_string()))
    }

    fn assign(&mut self, identifier: &str, value: Value) -> Result<(), EvalError> {
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
    env.define("clock".to_string(), Some(
        Value::Function {
            name: "clock".to_string(),
            arity: 0,
            body: FunctionBody::PrimitiveFunction(clock_primitive),
        }),
    );
    evaluate_statements(&program.statements, out, &mut env)
}

fn clock_primitive(_: Vec<Value>) -> Result<Value, EvalError> {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => Ok(Value::Number(duration.as_secs() as f64)),
        Err(err) => Err(EvalError::IOError(err.to_string())),
    }
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
            let val = expr
                .as_ref()
                .map(|expr| evaluate_expression(&expr, env))
                .transpose()?;
            env.define(identifier.to_string(), val);
        }
        Statement::If { condition, then_branch, else_branch } => {
            let condition_val = evaluate_expression(&condition, env)?;
            let val = value_truthiness(&condition_val);
            match (val, else_branch) {
                (true, _) => evaluate_statement(&then_branch, out, env)?,
                (false, Some(else_branch)) => evaluate_statement(&else_branch, out, env)?,
                _ => {},
            }
        }
        Statement::While { condition, body } => {
            while value_truthiness(&evaluate_expression(&condition, env)?) {
                evaluate_statement(body, out, env)?;
            }
        }
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
) -> Result<Value, EvalError> {
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
        Expression::Call { callee, arguments } => evaluate_function(callee, arguments, env),
    }
}

fn evaluate_literal(lit: &Literal, env: &Environment) -> Result<Value, EvalError> {
    match &lit {
        Literal::Number(x) => Ok(Value::Number(*x)),
        Literal::String(x) => Ok(Value::String(x.clone())),
        Literal::True => Ok(Value::Bool(true)),
        Literal::False => Ok(Value::Bool(false)),
        Literal::Nil => Ok(Value::Nil),
        Literal::Identifier(x) => env.identifier_value(x),
    }
}

fn evaluate_unary(
    op: &UnaryOperator,
    expr: &Expression,
    env: &mut Environment,
) -> Result<Value, EvalError> {
    let expr_val = evaluate_expression(expr, env)?;

    let incorrect_type_error = Err(EvalError::UnaryIncorrectTypes {
        op: op.clone(),
        expr: expr_val.clone(),
    });

    match op {
        // Lox
        UnaryOperator::Not => Ok(Value::Bool(!value_truthiness(&expr_val))),
        UnaryOperator::Negate => match &expr_val {
            Value::Number(x) => Ok(Value::Number(-x)),
            _ => incorrect_type_error,
        },
    }
}

fn evaluate_infix(
    op: &InfixOperator,
    lhs: &Expression,
    rhs: &Expression,
    env: &mut Environment,
) -> Result<Value, EvalError> {
    match op {
        InfixOperator::Equals => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (Value::Number(x), Value::Number(y)) =>
            {
                #[allow(clippy::float_cmp)]
                Ok(Value::Bool(x == y))
            }
            (Value::String(x), Value::String(y)) => {
                Ok(Value::Bool(x == y))
            }
            (Value::Bool(x), Value::Bool(y)) => {
                Ok(Value::Bool(x == y))
            }
            (Value::Nil, Value::Nil) => Ok(Value::Bool(true)),
            (lhs_val, rhs_val) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_val,
                rhs: rhs_val,
            }),
        },
        InfixOperator::NotEquals => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (Value::Number(x), Value::Number(y)) =>
            {
                #[allow(clippy::float_cmp)]
                Ok(Value::Bool(x != y))
            }
            (Value::String(x), Value::String(y)) => {
                Ok(Value::Bool(x != y))
            }
            (Value::Bool(x), Value::Bool(y)) => {
                Ok(Value::Bool(x != y))
            }
            (Value::Nil, Value::Nil) => Ok(Value::Bool(false)),
            (lhs_val, rhs_val) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_val,
                rhs: rhs_val,
            }),
        },
        InfixOperator::Less => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Bool(x < y)
        }),
        InfixOperator::LessEqual => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Bool(x <= y)
        }),
        InfixOperator::Greater => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Bool(x > y)
        }),
        InfixOperator::GreaterEqual => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Bool(x >= y)
        }),
        InfixOperator::Plus => match (evaluate_expression(lhs, env)?, evaluate_expression(rhs, env)?) {
            (Value::Number(x), Value::Number(y)) => {
                Ok(Value::Number(x + y))
            }
            (Value::String(x), Value::String(y)) => {
                Ok(Value::String(x + &y.to_string()))
            }
            (lhs_val, rhs_val) => Err(EvalError::InfixIncorrectTypes {
                op: op.clone(),
                lhs: lhs_val,
                rhs: rhs_val,
            }),
        },
        InfixOperator::Minus => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Number(x - y)
        }),
        InfixOperator::Times => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Number(x * y)
        }),
        InfixOperator::Divide => evaluate_numeric_infix(op, lhs, rhs, env, |x, y| {
            Value::Number(x / y)
        }),
        InfixOperator::Or => {
            let lhs_val = evaluate_expression(lhs, env)?;
            if value_truthiness(&lhs_val) {
                Ok(lhs_val)
            } else {
                evaluate_expression(rhs, env)
            }
        }
        InfixOperator::And => {
            let lhs_val = evaluate_expression(lhs, env)?;
            if !value_truthiness(&lhs_val) {
                Ok(lhs_val)
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
    f: fn (f64, f64) -> Value
) -> Result<Value, EvalError> {
    let lhs_val = evaluate_expression(lhs, env)?;
    let rhs_val = evaluate_expression(rhs, env)?;

    match (&lhs_val, &rhs_val) {
        (Value::Number(x), Value::Number(y)) => {
            Ok(f(*x, *y))
        }
        _ => Err(EvalError::InfixIncorrectTypes {
            op: op.clone(),
            lhs: lhs_val.clone(),
            rhs: rhs_val.clone(),
        }),
    }
}

fn evaluate_function(
    callee: &Expression,
    args: &Vec<Expression>,
    env: &mut Environment,
) -> Result<Value, EvalError> {
    let callee_val = evaluate_expression(callee, env)?;
    match callee_val {
        Value::Function { name, arity, body } => {
            if args.len() != arity {
                return Err(EvalError::IncorrectArity {
                    name,
                    arity,
                    got: args.len(),
                });
            }
            let arg_vals = args
                .iter()
                .map(|arg| evaluate_expression(arg, env))
                .collect::<Result<Vec<_>, _>>()?;
            match body {
                FunctionBody::PrimitiveFunction(f) => f(arg_vals),
            }
        },
        _ => Err(EvalError::ExpectedFunctionGot(callee_val)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    #[test]
    fn test_evaluate_program() {
        fn assert_success_output<S: Into<String>>(input: &str, expected_output: S) {
            let mut lexer = Lexer::new(input);
            lexer.lex().expect("lexing failed");
            let program = Parser::new(lexer.tokens).parse().expect("parse error");
            let mut buf = Vec::new();
            assert_eq!(evaluate_program(program, &mut buf), Ok(()));
            assert_eq!(String::from_utf8(buf), Ok(expected_output.into()));
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

        assert_success_output(
            r#"
              var x = 3;
              while (x > 0) {
                print x;
                x = x - 1;
              }
            "#,
            "3\n2\n1\n",
        );

        // For loop
        assert_success_output("for (var i = 0; i < 3; i = i + 1) print i;", "0\n1\n2\n");
        assert_success_output(
            r#"
              var i = 0;
              for (; i < 3;) {
                print i;
                i = i + 1;
              }
            "#,
            "0\n1\n2\n",
        );

        // N.B. This has a race condition. We should mock time in the
        // interpreter.
        assert_success_output(
            r#"
              var x = clock;
              print x();
            "#,
            format!("{}\n", SystemTime::now().duration_since(UNIX_EPOCH).expect("duration_since").as_secs()),
        );

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
