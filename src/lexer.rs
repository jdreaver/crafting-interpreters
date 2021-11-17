//! Lexer code to transform raw source code strings into tokens.
//!
//! The main function to use in this module is `lex`, which transforms
//! a raw source code string into `Token`s (or a `LexError`).

use std::{iter::FromIterator, num::ParseFloatError};

#[derive(Debug, PartialEq)]
pub enum Token {
    LeftBrace,
    RightBrace,

    LeftParen,
    RightParen,

    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Star,

    Bang,
    BangEqual,

    Equal,
    EqualEqual,

    Less,
    LessEqual,

    Greater,
    GreaterEqual,

    Slash,

    String(String),
    Identifier(String),
    Number(f64),

    And,
    Class,
    Else,
    False,
    For,
    Fun,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    UnknownChar(char),
    ParseFloatError(String, ParseFloatError),
    UnterminatedString,
}

/// LexPosition holds the current position for our lexer.
struct LexPosition {
    source: Vec<char>,
    position: usize,
}

impl LexPosition {
    fn new<S: Into<String>>(source: S) -> Self {
        LexPosition {
            source: source.into().chars().collect(),
            position: 0,
        }
    }

    /// View the next character but don't advance our current position
    fn peek(&self) -> Option<&char> {
        self.source.get(self.position)
    }

    fn advance(&mut self) {
        self.position += 1;
    }
}

pub fn lex<S: Into<String>>(source: S) -> Result<Vec<Token>, LexError> {
    let mut position = LexPosition::new(source);

    let mut tokens = Vec::new();

    fn single_tok(position: &mut LexPosition, tokens: &mut Vec<Token>, tok: Token) {
        tokens.push(tok);
        position.advance();
    }

    fn two_char_tok(position: &mut LexPosition, tokens: &mut Vec<Token>, single_tok: Token, c: char, double_tok: Token) {
        position.advance();
        if position.peek() == Some(&c) {
            tokens.push(double_tok);
            position.advance();
        } else {
            tokens.push(single_tok);
        }
    }

    while let Some(peeked) = position.peek() {
        match peeked {
            '{' => single_tok(&mut position, &mut tokens, Token::LeftBrace),
            '}' => single_tok(&mut position, &mut tokens, Token::RightBrace),
            '(' => single_tok(&mut position, &mut tokens, Token::LeftParen),
            ')' => single_tok(&mut position, &mut tokens, Token::RightParen),
            ',' => single_tok(&mut position, &mut tokens, Token::Comma),
            '.' => single_tok(&mut position, &mut tokens, Token::Dot),
            '-' => single_tok(&mut position, &mut tokens, Token::Minus),
            '+' => single_tok(&mut position, &mut tokens, Token::Plus),
            ';' => single_tok(&mut position, &mut tokens, Token::Semicolon),
            '*' => single_tok(&mut position, &mut tokens, Token::Star),
            '!' => two_char_tok(&mut position, &mut tokens, Token::Bang, '=', Token::BangEqual),
            '=' => two_char_tok(&mut position, &mut tokens, Token::Equal, '=', Token::EqualEqual),
            '<' => two_char_tok(&mut position, &mut tokens, Token::Less, '=', Token::LessEqual),
            '>' => two_char_tok(&mut position, &mut tokens, Token::Greater, '=', Token::GreaterEqual),
            '/' => {
                position.advance();
                if position.peek() == Some(&'/') {
                    eat_comment(&mut position);
                } else {
                    tokens.push(Token::Slash);
                }
            }
            '"' => tokens.push(string_token(&mut position).map(Token::String)?),
            &c if c.is_whitespace() => position.advance(),
            &c if c.is_numeric() => tokens.push(number_token(&mut position).map(Token::Number)?),
            &c if c.is_alphabetic() => tokens.push(identifier_or_reserved(&mut position)),
            &c => return Err(LexError::UnknownChar(c)),
        }
    }

    Ok(tokens)
}

#[test]
fn test_lex() {
    // Token salad
    assert_eq!(
        lex("{} hello () .-+; !!=! <><=>=>"),
        Ok(vec![
            Token::LeftBrace,
            Token::RightBrace,
            Token::Identifier("hello".to_string()),
            Token::LeftParen,
            Token::RightParen,
            Token::Dot,
            Token::Minus,
            Token::Plus,
            Token::Semicolon,
            Token::Bang,
            Token::BangEqual,
            Token::Bang,
            Token::Less,
            Token::Greater,
            Token::LessEqual,
            Token::GreaterEqual,
            Token::Greater,
        ])
    );

    // Comments
    assert_eq!(
        lex("/123//Hello\n//Ignore\n456"),
        Ok(vec![
            Token::Slash,
            Token::Number(123.0),
            Token::Number(456.0),
        ])
    );

    // Unterminated string
    assert_eq!(lex("\"nope"), Err(LexError::UnterminatedString));
}

fn eat_comment(position: &mut LexPosition) {
    while let Some(&c) = position.peek() {
        if c == '\n' {
            return;
        }
        position.advance();
    }
}

fn string_token(position: &mut LexPosition) -> Result<String, LexError> {
    // Invariant: we should be on the opening quote
    assert_eq!(position.peek(), Some(&'"'));
    position.advance();

    let mut str_vec = Vec::new();
    while let Some(&c) = position.peek() {
        position.advance();
        if c == '"' {
            return Ok(String::from_iter(str_vec));
        }
        str_vec.push(c);
    }

    // If we get here, we ran out of input before we saw a closing
    // quote
    Err(LexError::UnterminatedString)
}

fn number_token(position: &mut LexPosition) -> Result<f64, LexError> {
    let mut num_chars = Vec::<char>::new();
    while let Some(&c) = position.peek() {
        if c.is_numeric() || c == '.' {
            num_chars.push(c);
            position.advance();
        } else {
            break;
        }
    }

    let num_str = String::from_iter(num_chars);
    num_str
        .parse::<f64>()
        .map_err(|err| LexError::ParseFloatError(num_str, err))
}

fn identifier_or_reserved(position: &mut LexPosition) -> Token {
    let mut chars = Vec::<char>::new();
    while let Some(&c) = position.peek() {
        if c.is_alphanumeric() {
            chars.push(c);
            position.advance();
        } else {
            break;
        }
    }

    match String::from_iter(chars).as_str() {
        "and" => Token::And,
        "class" => Token::Class,
        "else" => Token::Else,
        "false" => Token::False,
        "for" => Token::For,
        "fun" => Token::Fun,
        "if" => Token::If,
        "nil" => Token::Nil,
        "or" => Token::Or,
        "print" => Token::Print,
        "return" => Token::Return,
        "super" => Token::Super,
        "this" => Token::This,
        "true" => Token::True,
        "var" => Token::Var,
        "while" => Token::While,
        s => Token::Identifier(s.to_string()),
    }
}
