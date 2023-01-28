#[derive(PartialEq, Debug, Clone)]
pub enum Token {
    Illegal,
    EOF,

    // Identifiers + literals
    Ident(String),
    Int(i64),

    // Booleans
    True,
    False,

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    EQ,
    NotEq,

    LT,
    GT,

    // Delimiters
    Comma,
    Semicolon,

    LParen,
    RParen,
    RBrace,
    LBrace,

    // Keywords
    Function,
    Let,
    If,
    Else,
    Return,
}
