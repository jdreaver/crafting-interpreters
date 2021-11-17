use std::{iter::FromIterator, num::ParseFloatError};

#[derive(Debug)]
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
    Identifier(String),
    Number(f64),
}

#[derive(Debug)]
pub enum LexError {
    UnknownChar(char),
    ParseFloatError(String, ParseFloatError),
}

// /// TokenContext holds a token and contextual information like its
// /// position in the source file.
// struct TokenContext {
//     token: Token,
//     line: u8,
//     column: u8,
// }

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

    // fn done(self) -> bool {
    //     self.peek().is_none()
    // }
}

pub fn lex<S: Into<String>>(source: S) -> Result<Vec<Token>, LexError> {
    let mut position = LexPosition::new(source);

    let mut tokens = Vec::new();

    while let Some(c) = position.peek() {
        match c {
            '{' => {
                tokens.push(Token::LeftBrace);
                position.advance();
            }
            '}' => {
                tokens.push(Token::RightBrace);
                position.advance();
            }
            '(' => {
                tokens.push(Token::LeftParen);
                position.advance();
            }
            ')' => {
                tokens.push(Token::RightParen);
                position.advance();
            }
            ',' => {
                tokens.push(Token::Comma);
                position.advance();
            }
            '.' => {
                tokens.push(Token::Dot);
                position.advance();
            }
            '-' => {
                tokens.push(Token::Minus);
                position.advance();
            }
            '+' => {
                tokens.push(Token::Plus);
                position.advance();
            }
            ';' => {
                tokens.push(Token::Semicolon);
                position.advance();
            }
            '*' => {
                tokens.push(Token::Star);
                position.advance();
            }
            &c if c.is_whitespace() => {
                position.advance();
            }
            &c if c.is_numeric() => tokens.push(number_token(&mut position).map(Token::Number)?),
            &c if c.is_alphabetic() => {
                tokens.push(Token::Identifier(identifier(&mut position)));
            }
            &c => return Err(LexError::UnknownChar(c)),
        }
    }

    Ok(tokens)
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

fn identifier(position: &mut LexPosition) -> String {
    let mut chars = Vec::<char>::new();
    while let Some(&c) = position.peek() {
        if c.is_alphanumeric() {
            chars.push(c);
            position.advance();
        } else {
            break;
        }
    }

    String::from_iter(chars)
}
