use crate::lexer::{Token, TokenValue};

// TODO: Add positions to Expression and other enums, but make sure to
// DRY with some kind of Positioned<T> type with the Token and
// LexError.

#[derive(Debug, PartialEq)]
pub enum Expression {
    Parens {
        expr: Box<Expression>,
    },
    Infix {
        lhs: Box<Expression>,
        op: InfixOperator,
        rhs: Box<Expression>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expression>,
    },
    Literal(Literal),
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum UnaryOperator {
    Not,
    Negate,
}

#[derive(Debug, PartialEq)]
pub enum Literal {
    Number(f64),
    String(String),
    Identifier(String),
    True,
    False,
    Nil,
}

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnexpectedToken(Token),
    UnexpectedTokenExpected { got: Token, want: TokenValue },
    OutOfInput,
    ExtraInput(Vec<Token>),
}

pub struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, index: 0 }
    }

    pub fn parse(&mut self) -> Result<Expression, ParseError> {
        match self.parse_expression() {
            Ok(expr) => {
                // Assert not input left
                if self.peek().is_some() {
                    Err(ParseError::ExtraInput(self.tokens[self.index..].to_vec()))
                } else {
                    Ok(expr)
                }
            }
            Err(err) => Err(err),
        }
    }

    /// Parses an expression using the following grammar and precedence rules:
    ///
    /// ```text
    /// expression     → equality ;
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
        self.parse_unary()
    }

    fn parse_unary(&mut self) -> Result<Expression, ParseError> {
        match self.peek_require()? {
            tok => match tok.value {
                TokenValue::Bang => self.parse_unary_inner(UnaryOperator::Not),
                TokenValue::Minus => self.parse_unary_inner(UnaryOperator::Negate),
                _ => self.parse_primary(),
            }
        }
    }

    fn parse_unary_inner(&mut self, op: UnaryOperator) -> Result<Expression, ParseError> {
        self.advance();
        let expr = Box::new(self.parse_unary()?);
        Ok(Expression::Unary{op, expr})
    }

    fn parse_primary(&mut self) -> Result<Expression, ParseError> {
        match self.peek_require()? {
            tok => {
                // TODO: This clone is unfortunate (I think? maybe it
                // is necessary). Try to get rid of it and see what
                // happens.
                let tok = tok.clone();
                match tok.value {
                    TokenValue::Number(num) => {
                        self.advance();
                        Ok(Expression::Literal(Literal::Number(num)))
                    }
                    TokenValue::String(string) => {
                        self.advance();
                        Ok(Expression::Literal(Literal::String(string)))
                    }
                    TokenValue::LeftParen => self.parenthesized_expression(&tok),
                    _ => Err(ParseError::UnexpectedToken(tok)),
                }
            }
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

    fn advance(&mut self) {
        self.index += 1;
    }

    fn parenthesized_expression(&mut self, start: &Token) -> Result<Expression, ParseError> {
        assert_eq!(start.value, TokenValue::LeftParen);
        self.advance();

        let expr = self.parse_expression()?;
        match self.peek() {
            None => Err(ParseError::OutOfInput),
            Some(tok) => match tok.value.clone() {
                TokenValue::RightParen => {
                    self.advance();
                    Ok(expr)
                }
                _ => Err(ParseError::UnexpectedTokenExpected {
                    got: tok.clone(),
                    want: TokenValue::RightParen,
                }),
            },
        }
    }
}
