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
    Block(Vec::<Statement>),
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
            Ok(Program {statements})
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
                    want: TokenValue::Identifier("IDENTIFIER".to_string())
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

        self.expect_semicolon()?;
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
                self.expect_semicolon()?;
                Ok(Statement::Print(expr))
            }
            TokenValue::LeftBrace => self.parse_block(&tok),
            _ => {
                let expr = self.parse_expression()?;
                self.expect_semicolon()?;
                Ok(Statement::Expression(expr))
            },
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

    fn expect_semicolon(&mut self) -> Result<(), ParseError> {
        let ending_tok = self.peek_require()?;
        match ending_tok.value {
            TokenValue::Semicolon => {
                self.advance();
                Ok(())
            }
            _ => Err(ParseError::UnexpectedTokenExpected {
                got: ending_tok.clone(),
                want: TokenValue::Semicolon,
            }),
        }
    }

    /// Parses an expression using the following grammar and precedence rules:
    ///
    /// ```text
    /// expression     → assignment ;
    /// assignment     → IDENTIFIER "=" assignment
    ///                | equality ;
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
        let lvalue = self.parse_equality()?;
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
            }
        }

    }

    fn parse_equality(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_comparison()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::EqualEqual => self.parse_infix_inner(lhs, InfixOperator::Equals, Parser::parse_equality),
                TokenValue::BangEqual => self.parse_infix_inner(lhs, InfixOperator::NotEquals, Parser::parse_equality),
                _ => Ok(lhs),
            },
        }
    }

    fn parse_comparison(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_term()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Less => self.parse_infix_inner(lhs, InfixOperator::Less, Parser::parse_comparison),
                TokenValue::LessEqual => self.parse_infix_inner(lhs, InfixOperator::LessEqual, Parser::parse_comparison),
                TokenValue::Greater => self.parse_infix_inner(lhs, InfixOperator::Greater, Parser::parse_comparison),
                TokenValue::GreaterEqual => self.parse_infix_inner(lhs, InfixOperator::GreaterEqual, Parser::parse_comparison),
                _ => Ok(lhs),
            },
        }
    }

    fn parse_term(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_factor()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Plus => self.parse_infix_inner(lhs, InfixOperator::Plus, Parser::parse_term),
                TokenValue::Minus => self.parse_infix_inner(lhs, InfixOperator::Minus, Parser::parse_term),
                _ => Ok(lhs),
            },
        }
    }

    fn parse_factor(&mut self) -> Result<Expression, ParseError> {
        let lhs = self.parse_unary()?;
        match self.peek() {
            None => Ok(lhs),
            Some(tok) => match tok.value {
                TokenValue::Slash => self.parse_infix_inner(lhs, InfixOperator::Divide, Parser::parse_factor),
                TokenValue::Star => self.parse_infix_inner(lhs, InfixOperator::Times, Parser::parse_factor),
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
        let tok = self.peek_require()?;
        match tok.value {
            TokenValue::RightParen => {
                self.advance();
                Ok(Expression::Parens(Box::new(expr)))
            }
            _ => Err(ParseError::UnexpectedTokenExpected {
                got: tok.clone(),
                want: TokenValue::RightParen,
            }),
        }
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

        assert_helper("1 + 1;", Program {
            statements: vec![
                Statement::Expression(
                    Expression::Infix {
                        op: InfixOperator::Plus,
                        lhs: Box::new(Expression::Literal(Literal::Number(1.0))),
                        rhs: Box::new(Expression::Literal(Literal::Number(1.0))),
                    }
                )
            ],
        });

        assert_helper("{1;}", Program {
            statements: vec![
                Statement::Block(
                    vec![
                        Statement::Expression(Expression::Literal(Literal::Number(1.0))),
                    ],
                )
            ],
        });

        let x_eq_1 = Statement::Declaration{
            identifier: "x".to_string(),
            expr: Some(Expression::Literal(Literal::Number(1.0))),
        };
        assert_helper("var x = 1;", Program {
            statements: vec![x_eq_1.clone()],
        });

        let print_bob = Statement::Print(
            Expression::Literal(Literal::Identifier("bob".to_string()))
        );
        assert_helper("var x = 1;\nprint bob;", Program {
            statements: vec![x_eq_1, print_bob],
        });

    }
 }
