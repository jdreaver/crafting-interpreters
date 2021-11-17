//! Lexer code to transform raw source code strings into tokens.
//!
//! The main function to use in this module is `lex`, which transforms
//! a raw source code string into `Token`s (or a `LexError`).

use std::{iter::FromIterator, num::ParseFloatError};

#[derive(Debug, PartialEq)]
pub struct Token {
    value: TokenValue,
    start: Position,
    end: Position,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Position {
    line: usize,
    column: usize,
}

#[derive(Debug, PartialEq)]
pub enum TokenValue {
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
pub struct LexError {
    error: LexErrorValue,
    start: Position,
    end: Position,
}

#[derive(Debug, PartialEq)]
pub enum LexErrorValue {
    UnknownChar(char),
    ParseFloatError(String, ParseFloatError),
    UnterminatedString,
}

/// LexPosition holds the current position for our lexer.
struct LexPosition {
    source: Vec<(Position, char)>,
    index: usize,
}

impl LexPosition {
    fn new<S: Into<String>>(source: S) -> Self {
        LexPosition {
            source: position_chars(source),
            index: 0,
        }
    }

    /// View the next character but don't advance our current position
    fn peek(&self) -> Option<&(Position, char)> {
        self.source.get(self.index)
    }

    fn advance(&mut self) {
        self.index += 1;
    }
}

/// Computes the line and column numbers for each character in the
/// input string.
fn position_chars<S: Into<String>>(source: S) -> Vec<(Position, char)> {
    source
        .into()
        .lines()
        .enumerate()
        .flat_map(|(line_num, line)| {
            line.chars().enumerate().map(move |(col, c)| {
                (
                    Position {
                        line: line_num + 1,
                        column: col + 1,
                    },
                    c,
                )
            })
        })
        .collect()
}

pub fn lex<S: Into<String>>(source: S) -> Result<Vec<Token>, LexError> {
    let mut position = LexPosition::new(source);

    let mut tokens = Vec::<Token>::new();

    fn make_single_tok(value: TokenValue, start: Position) -> Token {
        Token {
            value,
            start,
            end: start,
        }
    }

    fn make_double_tok(value: TokenValue, start: Position) -> Token {
        Token {
            value,
            start,
            end: Position {
                line: start.line,
                column: start.column + 1,
            },
        }
    }

    fn single_tok(
        position: &mut LexPosition,
        tokens: &mut Vec<Token>,
        value: TokenValue,
        start: Position,
    ) {
        tokens.push(make_single_tok(value, start));
        position.advance();
    }

    fn two_char_tok(
        position: &mut LexPosition,
        tokens: &mut Vec<Token>,
        single_val: TokenValue,
        c: char,
        double_val: TokenValue,
        start: Position,
    ) {
        position.advance();
        if position.peek().map(|p| p.1) == Some(c) {
            tokens.push(make_double_tok(double_val, start));
            position.advance();
        } else {
            tokens.push(make_single_tok(single_val, start));
        }
    }

    while let Some(&start) = position.peek() {
        let (start_pos, peeked) = start;
        match peeked {
            '{' => single_tok(&mut position, &mut tokens, TokenValue::LeftBrace, start_pos),
            '}' => single_tok(
                &mut position,
                &mut tokens,
                TokenValue::RightBrace,
                start_pos,
            ),
            '(' => single_tok(&mut position, &mut tokens, TokenValue::LeftParen, start_pos),
            ')' => single_tok(
                &mut position,
                &mut tokens,
                TokenValue::RightParen,
                start_pos,
            ),
            ',' => single_tok(&mut position, &mut tokens, TokenValue::Comma, start_pos),
            '.' => single_tok(&mut position, &mut tokens, TokenValue::Dot, start_pos),
            '-' => single_tok(&mut position, &mut tokens, TokenValue::Minus, start_pos),
            '+' => single_tok(&mut position, &mut tokens, TokenValue::Plus, start_pos),
            ';' => single_tok(&mut position, &mut tokens, TokenValue::Semicolon, start_pos),
            '*' => single_tok(&mut position, &mut tokens, TokenValue::Star, start_pos),
            '!' => two_char_tok(
                &mut position,
                &mut tokens,
                TokenValue::Bang,
                '=',
                TokenValue::BangEqual,
                start_pos,
            ),
            '=' => two_char_tok(
                &mut position,
                &mut tokens,
                TokenValue::Equal,
                '=',
                TokenValue::EqualEqual,
                start_pos,
            ),
            '<' => two_char_tok(
                &mut position,
                &mut tokens,
                TokenValue::Less,
                '=',
                TokenValue::LessEqual,
                start_pos,
            ),
            '>' => two_char_tok(
                &mut position,
                &mut tokens,
                TokenValue::Greater,
                '=',
                TokenValue::GreaterEqual,
                start_pos,
            ),
            '/' => {
                position.advance();
                if position.peek().map(|p| p.1) == Some('/') {
                    eat_comment(&mut position, &start_pos);
                } else {
                    tokens.push(make_single_tok(TokenValue::Slash, start_pos));
                }
            }
            '"' => tokens.push(string_token(&mut position, &start)?),
            c if c.is_whitespace() => position.advance(),
            c if c.is_numeric() => tokens.push(number_token(&mut position, &start_pos)?),
            c if c.is_alphabetic() => {
                tokens.push(identifier_or_reserved(&mut position, &start_pos))
            }
            c => {
                return Err(LexError {
                    error: LexErrorValue::UnknownChar(c),
                    start: start_pos,
                    end: start_pos,
                })
            }
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
            Token {
                value: TokenValue::LeftBrace,
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            },
            Token {
                value: TokenValue::RightBrace,
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 2 }
            },
            Token {
                value: TokenValue::Identifier("hello".to_string()),
                start: Position { line: 1, column: 4 },
                end: Position { line: 1, column: 8 }
            },
            Token {
                value: TokenValue::LeftParen,
                start: Position {
                    line: 1,
                    column: 10
                },
                end: Position {
                    line: 1,
                    column: 10
                }
            },
            Token {
                value: TokenValue::RightParen,
                start: Position {
                    line: 1,
                    column: 11
                },
                end: Position {
                    line: 1,
                    column: 11
                }
            },
            Token {
                value: TokenValue::Dot,
                start: Position {
                    line: 1,
                    column: 13
                },
                end: Position {
                    line: 1,
                    column: 13
                }
            },
            Token {
                value: TokenValue::Minus,
                start: Position {
                    line: 1,
                    column: 14
                },
                end: Position {
                    line: 1,
                    column: 14
                }
            },
            Token {
                value: TokenValue::Plus,
                start: Position {
                    line: 1,
                    column: 15
                },
                end: Position {
                    line: 1,
                    column: 15
                }
            },
            Token {
                value: TokenValue::Semicolon,
                start: Position {
                    line: 1,
                    column: 16
                },
                end: Position {
                    line: 1,
                    column: 16
                }
            },
            Token {
                value: TokenValue::Bang,
                start: Position {
                    line: 1,
                    column: 18
                },
                end: Position {
                    line: 1,
                    column: 18
                }
            },
            Token {
                value: TokenValue::BangEqual,
                start: Position {
                    line: 1,
                    column: 19
                },
                end: Position {
                    line: 1,
                    column: 20
                }
            },
            Token {
                value: TokenValue::Bang,
                start: Position {
                    line: 1,
                    column: 21
                },
                end: Position {
                    line: 1,
                    column: 21
                }
            },
            Token {
                value: TokenValue::Less,
                start: Position {
                    line: 1,
                    column: 23
                },
                end: Position {
                    line: 1,
                    column: 23
                }
            },
            Token {
                value: TokenValue::Greater,
                start: Position {
                    line: 1,
                    column: 24
                },
                end: Position {
                    line: 1,
                    column: 24
                }
            },
            Token {
                value: TokenValue::LessEqual,
                start: Position {
                    line: 1,
                    column: 25
                },
                end: Position {
                    line: 1,
                    column: 26
                }
            },
            Token {
                value: TokenValue::GreaterEqual,
                start: Position {
                    line: 1,
                    column: 27
                },
                end: Position {
                    line: 1,
                    column: 28
                }
            },
            Token {
                value: TokenValue::Greater,
                start: Position {
                    line: 1,
                    column: 29
                },
                end: Position {
                    line: 1,
                    column: 29
                }
            },
        ])
    );

    // Comments
    assert_eq!(
        lex("/123//Hello\n//Ignore\n456"),
        Ok(vec![
            Token {
                value: TokenValue::Slash,
                start: Position { line: 1, column: 1 },
                end: Position { line: 1, column: 1 }
            },
            Token {
                value: TokenValue::Number(123.0),
                start: Position { line: 1, column: 2 },
                end: Position { line: 1, column: 4 }
            },
            Token {
                value: TokenValue::Number(456.0),
                start: Position { line: 3, column: 1 },
                end: Position { line: 3, column: 3 }
            },
        ])
    );

    // Unknown char
    assert_eq!(
        lex("™"),
        Err(LexError {
            error: LexErrorValue::UnknownChar('™'),
            start: Position { line: 1, column: 1 },
            end: Position { line: 1, column: 1 }
        })
    );

    // Unterminated string
    assert_eq!(
        lex("\"nope"),
        Err(LexError {
            error: LexErrorValue::UnterminatedString,
            start: Position { line: 1, column: 1 },
            end: Position { line: 1, column: 5 }
        })
    );
}

fn eat_comment(position: &mut LexPosition, start: &Position) {
    while let Some(&(pos, _)) = position.peek() {
        if pos.line != start.line {
            return;
        }
        position.advance();
    }
}

fn string_token(
    position: &mut LexPosition,
    &(start, start_char): &(Position, char),
) -> Result<Token, LexError> {
    // Invariant: we should be on the opening quote
    assert_eq!(start_char, '"');
    position.advance();

    let mut str_vec = Vec::new();
    let mut last_pos = start;
    while let Some(&(pos, c)) = position.peek() {
        position.advance();
        if c == '"' {
            return Ok(Token {
                value: TokenValue::String(String::from_iter(str_vec)),
                start,
                end: pos,
            });
        }
        str_vec.push(c);
        last_pos = pos;
    }

    // If we get here, we ran out of input before we saw a closing
    // quote
    Err(LexError { error: LexErrorValue::UnterminatedString, start, end: last_pos })
}

fn number_token(position: &mut LexPosition, &start: &Position) -> Result<Token, LexError> {
    let mut end = start;
    let mut num_chars = Vec::<char>::new();
    while let Some(&(pos, c)) = position.peek() {
        if c.is_numeric() || c == '.' {
            num_chars.push(c);
            end = pos;
            position.advance();
        } else {
            break;
        }
    }

    let num_str = String::from_iter(num_chars);
    num_str
        .parse::<f64>()
        .map(|f| Token {
            value: TokenValue::Number(f),
            start,
            end,
        })
        .map_err(|err| LexError {
            error: LexErrorValue::ParseFloatError(num_str, err),
            start,
            end,
        })
}

fn identifier_or_reserved(position: &mut LexPosition, &start: &Position) -> Token {
    let mut end = start;
    let mut chars = Vec::<char>::new();
    while let Some(&(pos, c)) = position.peek() {
        if c.is_alphanumeric() {
            chars.push(c);
            end = pos;
            position.advance();
        } else {
            break;
        }
    }

    let value = match String::from_iter(chars).as_str() {
        "and" => TokenValue::And,
        "class" => TokenValue::Class,
        "else" => TokenValue::Else,
        "false" => TokenValue::False,
        "for" => TokenValue::For,
        "fun" => TokenValue::Fun,
        "if" => TokenValue::If,
        "nil" => TokenValue::Nil,
        "or" => TokenValue::Or,
        "print" => TokenValue::Print,
        "return" => TokenValue::Return,
        "super" => TokenValue::Super,
        "this" => TokenValue::This,
        "true" => TokenValue::True,
        "var" => TokenValue::Var,
        "while" => TokenValue::While,
        s => TokenValue::Identifier(s.to_string()),
    };
    Token { value, start, end }
}
