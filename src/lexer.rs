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

#[derive(Debug)]
pub enum LexError {
    UnknownChar(char),
    ParseFloatError(String, ParseFloatError),
    UnterminatedString,
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
            // TODO: Figure out how to DRY single tokens, two char
            // tokens, etc
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
            '!' => {
                position.advance();
                if position.peek() == Some(&'=') {
                    tokens.push(Token::BangEqual);
                    position.advance();
                } else {
                    tokens.push(Token::Bang);
                }
            }
            '=' => {
                position.advance();
                if position.peek() == Some(&'=') {
                    tokens.push(Token::EqualEqual);
                    position.advance();
                } else {
                    tokens.push(Token::Equal);
                }
            }
            '<' => {
                position.advance();
                if position.peek() == Some(&'=') {
                    tokens.push(Token::LessEqual);
                    position.advance();
                } else {
                    tokens.push(Token::Less);
                }
            }
            '>' => {
                position.advance();
                if position.peek() == Some(&'=') {
                    tokens.push(Token::GreaterEqual);
                    position.advance();
                } else {
                    tokens.push(Token::Greater);
                }
            }
            '/' => {
                position.advance();
                if position.peek() == Some(&'/') {
                    eat_comment(&mut position);
                } else {
                    tokens.push(Token::Slash);
                }
            }
            '"' => tokens.push(string_token(&mut position).map(Token::String)?),
            &c if c.is_whitespace() => {
                position.advance();
            }
            &c if c.is_numeric() => tokens.push(number_token(&mut position).map(Token::Number)?),
            &c if c.is_alphabetic() => tokens.push(identifier_or_reserved(&mut position)),
            &c => return Err(LexError::UnknownChar(c)),
        }
    }

    Ok(tokens)
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
        s => Token::String(s.to_string()),
    }
}
