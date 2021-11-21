use crate::lexer::{Token, TokenValue};

// TODO: Add positions to parsed types, but make sure to DRY with some
// kind of Positioned<T> type with the Token and LexError.

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Expression(Expression),
    Print(Expression),
    Declaration {
        identifier: String,
        expr: Option<Expression>,
    },
    If {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },
    While {
        condition: Expression,
        body: Box<Statement>,
    },
    Function {
        name: String,
        params: Vec<String>,
        body: Vec<Statement>,
    },
    Block(Vec<Statement>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Parens(Box<Expression>),
    Assignment {
        target: String,
        expr: Box<Expression>,
    },
    Infix {
        op: InfixOperator,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expression>,
    },
    Call {
        callee: Box<Expression>,
        arguments: Vec<Expression>,
    },
    Literal(Literal),
}

#[derive(Debug, PartialEq, Clone)]
pub enum InfixOperator {
    Equals,
    NotEquals,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Plus,
    Minus,
    Times,
    Divide,
    Or,
    And,
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryOperator {
    Not,
    Negate,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    Number(f64),
    String(String),
    Identifier(String),
    True,
    False,
    Nil,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ParseError {
    UnexpectedToken(Token),
    UnexpectedTokenExpected { got: Token, want: TokenValue },
    OutOfInput(String),
    ExtraInput(Vec<Token>),
    InvalidAssignmentTarget(Expression),
}

pub struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, index: 0 }
    }

    pub fn parse(&mut self) -> Result<Program, ParseError> {
        let mut statements = Vec::new();
        while !self.at_end() {
            statements.push(self.parse_declaration()?)
        }

        // Assert no input left
        if self.peek().is_some() {
            Err(ParseError::ExtraInput(self.tokens[self.index..].to_vec()))
        } else {
            Ok(Program { statements })
        }
    }

    fn parse_declaration(&mut self) -> Result<Statement, ParseError> {
        let tok = self.peek_require("parse_declaration")?;
        match tok.value {
            TokenValue::Var => self.parse_var_declaration(),
            TokenValue::Fun => self.parse_function_declaration(),
            _ => self.parse_statement(),
        }
    }

    fn parse_var_declaration(&mut self) -> Result<Statement, ParseError> {
        self.expect_token("parse_var_declaration var", TokenValue::Var)?;

        let ident = self.expect_identifier("parse_var_declaration")?;

        let eq_token = self.peek_require("parse_var_declaration equal")?;
        let expr = match eq_token.value {
            TokenValue::Equal => {
                self.advance();
                Some(self.parse_expression()?)
            }
            _ => None,
        };

        self.expect_token("parse_var_declaration", TokenValue::Semicolon)?;
        Ok(Statement::Declaration {
            identifier: ident.to_string(),
            expr,
        })
    }

    fn parse_function_declaration(&mut self) -> Result<Statement, ParseError> {
        self.expect_token("parse_function_declaration fun", TokenValue::Fun)?;

        let name = self.expect_identifier("parse_function_declaration")?;
        self.expect_token("parse_function_declaration left paren", TokenValue::LeftParen)?;

        let mut params = Vec::new();
        if self.peek_require("parse_function_declaration immediate right paren")?.value != TokenValue::RightParen {
            loop {
                params.push(self.expect_identifier("function params")?);
                if self.peek_require("function params comma")?.value == TokenValue::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        self.expect_token("parse_function_declaration right paren", TokenValue::RightParen)?;

        let body = self.parse_block_inner()?;

        Ok(Statement::Function { name, params, body })
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        let tok = self.peek_require("parse statement")?.clone();
        match tok.value {
            TokenValue::Print => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect_token("parse_statement print", TokenValue::Semicolon)?;
                Ok(Statement::Print(expr))
            }
            TokenValue::If => self.parse_if(),
            TokenValue::While => self.parse_while(),
            TokenValue::For => self.parse_for(),
            TokenValue::LeftBrace => self.parse_block(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expr = self.parse_expression()?;
        self.expect_token("parse_expression_statement", TokenValue::Semicolon)?;
        Ok(Statement::Expression(expr))
    }

    fn parse_if(&mut self) -> Result<Statement, ParseError> {
        self.expect_token("parse_if if", TokenValue::If)?;

        self.expect_token("parse_if left paren", TokenValue::LeftParen)?;
        let condition = self.parse_expression()?;
        self.expect_token("parse_if right paren", TokenValue::RightParen)?;

        let then_branch = Box::new(self.parse_statement()?);
        let else_branch = if self.peek().map(|t| t.value.clone()) == Some(TokenValue::Else) {
            self.advance();
            Some(Box::new(self.parse_statement()?))
        } else {
            None
        };

        Ok(Statement::If {
            condition,
            then_branch,
            else_branch,
        })
    }

    fn parse_while(&mut self) -> Result<Statement, ParseError> {
        self.expect_token("parse_while while", TokenValue::While)?;

        self.expect_token("parse_while left paren", TokenValue::LeftParen)?;
        let condition = self.parse_expression()?;
        self.expect_token("parse_while right paren", TokenValue::RightParen)?;

        let body = Box::new(self.parse_statement()?);

        Ok(Statement::While { condition, body })
    }

    // For is just syntactic sugar for a while loop
    fn parse_for(&mut self) -> Result<Statement, ParseError> {
        self.expect_token("parse_for for", TokenValue::For)?;

        self.expect_token("parse_for left paren", TokenValue::LeftParen)?;

        let initializer: Option<Statement> = match self.peek_require("parse_for initializer")?.value {
            TokenValue::Semicolon => {
                self.advance();
                None
            },
            TokenValue::Var => Some(self.parse_declaration()?),
            _ => Some(self.parse_expression_statement()?),
        };

        let condition: Option<Expression> = match self.peek_require("parse_for condition")?.value {
            TokenValue::Semicolon => {
                self.advance();
                None
            },
            _ => {
                let expr = self.parse_expression()?;
                self.expect_token("parse_for condition semicolon", TokenValue::Semicolon)?;
                Some(expr)
            },
        };

        let increment: Option<Statement> = match self.peek_require("parse_for increment")?.value {
            TokenValue::RightParen => None,
            _ => Some(Statement::Expression(self.parse_expression()?)),
        };

        self.expect_token("parse_for right paren", TokenValue::RightParen)?;

        let mut body = self.parse_statement()?;

        // Desugar for(init; condition; increment) body to
        // {
        //   init
        //   while (condition) {
        //     body
        //     increment
        //   }
        // }
        match increment {
            None => {},
            Some(inc) => {
                body = Statement::Block(vec![body, inc]);
            }
        }

        let while_condition = condition.unwrap_or(Expression::Literal(Literal::True));
        let while_stmt = Statement::While {
            condition: while_condition,
            body: Box::new(body),
        };

        match initializer {
            Some(init) => Ok(Statement::Block(vec![init, while_stmt])),
            None => Ok(while_stmt),
        }
    }

    fn parse_block(&mut self) -> Result<Statement, ParseError> {
        Ok(Statement::Block(self.parse_block_inner()?))
    }

    fn parse_block_inner(&mut self) -> Result<Vec<Statement>, ParseError> {
        self.expect_token("parse_block left brace", TokenValue::LeftBrace)?;

        let mut statements = Vec::new();
        while self.peek_require("parse_block statements")?.value != TokenValue::RightBrace {
            statements.push(self.parse_declaration()?);
        }

        assert_eq!(self.peek_require("parse_block right brace")?.value, TokenValue::RightBrace);
        self.advance();

        Ok(statements)
    }

    fn expect_token<S: Into<String>>(&mut self, context: S, token_value: TokenValue) -> Result<(), ParseError> {
        let ending_tok = self.peek_require(format!("({}) expect_token {:?}", context.into(), token_value))?;
        if ending_tok.value == token_value {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedTokenExpected {
                got: ending_tok.clone(),
                want: token_value,
            })
        }
    }

    fn expect_identifier<S: Into<String>>(&mut self, context: S) -> Result<String, ParseError> {
        let tok = self.peek_require(format!("({}) expect_identifier", context.into()))?.clone();
        match tok.value {
            TokenValue::Identifier(ident) => {
                self.advance();
                Ok(ident)
            }
            _ => {
                return Err(ParseError::UnexpectedTokenExpected {
                    got: tok.clone(),
                    want: TokenValue::Identifier("IDENTIFIER".to_string()),
                })
            }
        }
    }

    /// Parses an expression using the following grammar and precedence rules:
    ///
    /// ```text
    /// expression     → assignment ;
    /// assignment     → IDENTIFIER "=" assignment
    ///                | logic_or ;
    /// logic_or       → logic_and ( "or" logic_and )* ;
    /// logic_and      → equality ( "and" equality )* ;
    /// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term           → factor ( ( "-" | "+" ) factor )* ;
    /// factor         → unary ( ( "/" | "*" ) unary )* ;
    /// unary          → ( "!" | "-" ) unary
    ///                | call ;
    /// call           → primary ( "(" arguments? ")" )* ;
    /// arguments      → expression ( "," expression )* ;
    /// primary        → NUMBER | STRING | "true" | "false" | "nil"
    ///                | "(" expression ")" ;
    /// ```
    fn parse_expression(&mut self) -> Result<Expression, ParseError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expression, ParseError> {
        let lvalue = self.parse_logical_or()?;
        match self.peek() {
            None => Ok(lvalue),
            Some(tok) => match tok.value {
                TokenValue::Equal => {
                    let target = match lvalue {
                        Expression::Literal(Literal::Identifier(ident)) => ident,
                        _ => return Err(ParseError::InvalidAssignmentTarget(lvalue)),
                    };
                    self.advance();
                    let expr = Box::new(self.parse_assignment()?);
                    Ok(Expression::Assignment { target, expr })
                }
                _ => Ok(lvalue),
            },
        }
    }

    fn parse_logical_or(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_logical_and()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Or => {
                    self.advance();
                    let rhs = self.parse_logical_and()?;
                    Ok(Expression::Infix {
                        op: InfixOperator::Or,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                }
                _ => Ok(lhs),
            },
        }
    }

    fn parse_logical_and(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_equality()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::And => {
                    self.advance();
                    let rhs = self.parse_equality()?;
                    Ok(Expression::Infix {
                        op: InfixOperator::And,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                }
                _ => Ok(lhs),
            },
        }
    }

    fn parse_equality(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_comparison()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::EqualEqual => {
                    self.parse_infix_inner(lhs, InfixOperator::Equals, Parser::parse_equality)
                }
                TokenValue::BangEqual => {
                    self.parse_infix_inner(lhs, InfixOperator::NotEquals, Parser::parse_equality)
                }
                _ => Ok(lhs),
            },
        }
    }

    fn parse_comparison(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_term()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Less => {
                    self.parse_infix_inner(lhs, InfixOperator::Less, Parser::parse_comparison)
                }
                TokenValue::LessEqual => {
                    self.parse_infix_inner(lhs, InfixOperator::LessEqual, Parser::parse_comparison)
                }
                TokenValue::Greater => {
                    self.parse_infix_inner(lhs, InfixOperator::Greater, Parser::parse_comparison)
                }
                TokenValue::GreaterEqual => self.parse_infix_inner(
                    lhs,
                    InfixOperator::GreaterEqual,
                    Parser::parse_comparison,
                ),
                _ => Ok(lhs),
            },
        }
    }

    fn parse_term(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_factor()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Plus => {
                    self.parse_infix_inner(lhs, InfixOperator::Plus, Parser::parse_term)
                }
                TokenValue::Minus => {
                    self.parse_infix_inner(lhs, InfixOperator::Minus, Parser::parse_term)
                }
                _ => Ok(lhs),
            },
        }
    }

    fn parse_factor(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_unary()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Slash => {
                    self.parse_infix_inner(lhs, InfixOperator::Divide, Parser::parse_factor)
                }
                TokenValue::Star => {
                    self.parse_infix_inner(lhs, InfixOperator::Times, Parser::parse_factor)
                }
                _ => Ok(lhs),
            },
        }
    }

    fn parse_infix_inner(
        &mut self,
        lhs: Expression,
        op: InfixOperator,
        parse_rhs: fn(&mut Parser) -> Result<Expression, ParseError>,
    ) -> Result<Expression, ParseError> {
        self.advance();
        let lhs = Box::new(lhs);
        let rhs = Box::new(parse_rhs(self)?);
        Ok(Expression::Infix { op, lhs, rhs })
    }

    fn parse_unary(&mut self) -> Result<Expression, ParseError> {
        let tok = self.peek_require("parse_unary")?;
        match tok.value {
            TokenValue::Bang => self.parse_unary_inner(UnaryOperator::Not),
            TokenValue::Minus => self.parse_unary_inner(UnaryOperator::Negate),
            _ => self.parse_call(),
        }
    }

    fn parse_unary_inner(&mut self, op: UnaryOperator) -> Result<Expression, ParseError> {
        self.advance();
        let expr = Box::new(self.parse_unary()?);
        Ok(Expression::Unary { op, expr })
    }

    fn parse_call(&mut self) -> Result<Expression, ParseError> {
        let mut expr = self.parse_primary()?;

        // There can be many function calls in a row
        while let Some(next_tok) = self.peek() {
            match next_tok.value {
                TokenValue::LeftParen => {
                    expr = self.finish_call(expr)?;
                }
                _ =>{
                    break
                }
            }
        }

        Ok(expr)
    }

    fn finish_call(&mut self, callee: Expression) -> Result<Expression, ParseError> {
        self.expect_token("finish_call left paren", TokenValue::LeftParen)?;

        let mut args = Vec::new();
        if self.peek_require("finish_call immediate right paren")?.value != TokenValue::RightParen {
            loop {
                args.push(self.parse_expression()?);
                if self.peek_require("finish_call args comma")?.value == TokenValue::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.expect_token("finish_call right paren", TokenValue::RightParen)?;

        Ok(Expression::Call {
            callee: Box::new(callee),
            arguments: args,
        })
    }

    fn parse_primary(&mut self) -> Result<Expression, ParseError> {
        let tok = self.peek_require("parse_primary")?.clone(); // TODO Try to remove clone() here
        match tok.value {
            TokenValue::Number(num) => {
                self.advance();
                Ok(Expression::Literal(Literal::Number(num)))
            }
            TokenValue::String(string) => {
                self.advance();
                Ok(Expression::Literal(Literal::String(string)))
            }
            TokenValue::Identifier(ident) => {
                self.advance();
                Ok(Expression::Literal(Literal::Identifier(ident)))
            }
            TokenValue::True => {
                self.advance();
                Ok(Expression::Literal(Literal::True))
            }
            TokenValue::False => {
                self.advance();
                Ok(Expression::Literal(Literal::False))
            }
            TokenValue::Nil => {
                self.advance();
                Ok(Expression::Literal(Literal::Nil))
            }
            TokenValue::LeftParen => self.parenthesized_expression(),
            _ => Err(ParseError::UnexpectedToken(tok)),
        }
    }

    /// View the next token but don't advance our current position
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }

    /// Like peek(), but returns an error if we reach end of input
    fn peek_require<S: Into<String>>(&self, description: S) -> Result<&Token, ParseError> {
        self.peek().ok_or(ParseError::OutOfInput(description.into()))
    }

    fn at_end(&self) -> bool {
        self.peek().is_none()
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn parenthesized_expression(&mut self) -> Result<Expression, ParseError> {
        self.expect_token("parenthesized_expression", TokenValue::LeftParen)?;
        let expr = self.parse_expression()?;
        self.expect_token("parenthesized_expression", TokenValue::RightParen)?;
        Ok(Expression::Parens(Box::new(expr)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;

    #[test]
    fn test_parse() {
        fn assert_helper(input: &str, expected: Program) {
            let mut lexer = Lexer::new(input);
            lexer.lex().expect("lexing failed");
            let program = Parser::new(lexer.tokens).parse();
            assert_eq!(program, Ok(expected));
        }

        assert_helper(
            "1 + 1;",
            Program {
                statements: vec![Statement::Expression(Expression::Infix {
                    op: InfixOperator::Plus,
                    lhs: Box::new(Expression::Literal(Literal::Number(1.0))),
                    rhs: Box::new(Expression::Literal(Literal::Number(1.0))),
                })],
            },
        );

        assert_helper(
            "{1;}",
            Program {
                statements: vec![Statement::Block(vec![Statement::Expression(
                    Expression::Literal(Literal::Number(1.0)),
                )])],
            },
        );

        let x_eq_1 = Statement::Declaration {
            identifier: "x".to_string(),
            expr: Some(Expression::Literal(Literal::Number(1.0))),
        };
        assert_helper(
            "var x = 1;",
            Program {
                statements: vec![x_eq_1.clone()],
            },
        );

        let print_bob =
            Statement::Print(Expression::Literal(Literal::Identifier("bob".to_string())));
        assert_helper(
            "var x = 1;\nprint bob;",
            Program {
                statements: vec![x_eq_1, print_bob],
            },
        );
    }
}
