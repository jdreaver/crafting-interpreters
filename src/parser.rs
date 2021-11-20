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
    OutOfInput,
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
        let tok = self.peek_require()?.clone();
        match tok.value {
            TokenValue::Var => self.parse_declaration_inner(&tok),
            _ => self.parse_statement(),
        }
    }

    fn parse_declaration_inner(&mut self, start: &Token) -> Result<Statement, ParseError> {
        assert_eq!(start.value, TokenValue::Var);
        self.advance();

        let ident_token = self.peek_require()?.clone();
        let identifier = match &ident_token.value {
            TokenValue::Identifier(ident) => {
                self.advance();
                ident
            }
            _ => {
                return Err(ParseError::UnexpectedTokenExpected {
                    got: ident_token.clone(),
                    want: TokenValue::Identifier("IDENTIFIER".to_string()),
                })
            }
        };

        let eq_token = self.peek_require()?;
        let expr = match eq_token.value {
            TokenValue::Equal => {
                self.advance();
                Some(self.parse_expression()?)
            }
            _ => None,
        };

        self.expect_token(TokenValue::Semicolon)?;
        Ok(Statement::Declaration {
            identifier: identifier.to_string(),
            expr,
        })
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        let tok = self.peek_require()?.clone();
        match tok.value {
            TokenValue::Print => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect_token(TokenValue::Semicolon)?;
                Ok(Statement::Print(expr))
            }
            TokenValue::If => self.parse_if(&tok),
            TokenValue::While => self.parse_while(&tok),
            TokenValue::For => self.parse_for(&tok),
            TokenValue::LeftBrace => self.parse_block(&tok),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expr = self.parse_expression()?;
        self.expect_token(TokenValue::Semicolon)?;
        Ok(Statement::Expression(expr))
    }

    fn parse_if(&mut self, start: &Token) -> Result<Statement, ParseError> {
        assert_eq!(start.value, TokenValue::If);
        self.advance();

        self.expect_token(TokenValue::LeftParen)?;
        let condition = self.parse_expression()?;
        self.expect_token(TokenValue::RightParen)?;

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

    fn parse_while(&mut self, start: &Token) -> Result<Statement, ParseError> {
        assert_eq!(start.value, TokenValue::While);
        self.advance();

        self.expect_token(TokenValue::LeftParen)?;
        let condition = self.parse_expression()?;
        self.expect_token(TokenValue::RightParen)?;

        let body = Box::new(self.parse_statement()?);

        Ok(Statement::While { condition, body })
    }

    // For is just syntactic sugar for a while loop
    fn parse_for(&mut self, start: &Token) -> Result<Statement, ParseError> {
        assert_eq!(start.value, TokenValue::For);
        self.advance();

        self.expect_token(TokenValue::LeftParen)?;

        let initializer: Option<Statement> = match self.peek_require()?.value {
            TokenValue::Semicolon => {
                self.advance();
                None
            },
            TokenValue::Var => Some(self.parse_declaration()?),
            _ => Some(self.parse_expression_statement()?),
        };

        let condition: Option<Expression> = match self.peek_require()?.value {
            TokenValue::Semicolon => {
                self.advance();
                None
            },
            _ => {
                let expr = self.parse_expression()?;
                self.expect_token(TokenValue::Semicolon)?;
                Some(expr)
            },
        };

        let increment: Option<Statement> = match self.peek_require()?.value {
            TokenValue::RightParen => None,
            _ => Some(Statement::Expression(self.parse_expression()?)),
        };

        self.expect_token(TokenValue::RightParen)?;

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

    fn parse_block(&mut self, start: &Token) -> Result<Statement, ParseError> {
        assert_eq!(start.value, TokenValue::LeftBrace);
        self.advance();

        let mut statements = Vec::new();
        while self.peek_require()?.value != TokenValue::RightBrace {
            statements.push(self.parse_declaration()?);
        }

        assert_eq!(self.peek_require()?.value, TokenValue::RightBrace);
        self.advance();

        Ok(Statement::Block(statements))
    }

    fn expect_token(&mut self, token_value: TokenValue) -> Result<(), ParseError> {
        let ending_tok = self.peek_require()?;
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
    ///                | primary ;
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
        let tok = self.peek_require()?;
        match tok.value {
            TokenValue::Bang => self.parse_unary_inner(UnaryOperator::Not),
            TokenValue::Minus => self.parse_unary_inner(UnaryOperator::Negate),
            _ => self.parse_primary(),
        }
    }

    fn parse_unary_inner(&mut self, op: UnaryOperator) -> Result<Expression, ParseError> {
        self.advance();
        let expr = Box::new(self.parse_unary()?);
        Ok(Expression::Unary { op, expr })
    }

    fn parse_primary(&mut self) -> Result<Expression, ParseError> {
        let tok = self.peek_require()?.clone(); // TODO Try to remove clone() here
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
            TokenValue::LeftParen => self.parenthesized_expression(&tok),
            _ => Err(ParseError::UnexpectedToken(tok)),
        }
    }

    /// View the next token but don't advance our current position
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }

    /// Like peek(), but returns an error if we reach end of input
    fn peek_require(&self) -> Result<&Token, ParseError> {
        self.peek().ok_or(ParseError::OutOfInput)
    }

    fn at_end(&self) -> bool {
        self.peek().is_none()
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn parenthesized_expression(&mut self, start: &Token) -> Result<Expression, ParseError> {
        assert_eq!(start.value, TokenValue::LeftParen);
        self.advance();

        let expr = self.parse_expression()?;
        self.expect_token(TokenValue::RightParen)?;
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
