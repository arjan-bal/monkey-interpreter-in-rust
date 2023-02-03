#[derive(PartialEq, Debug, Clone, Eq, Hash)]
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

impl Token {
    pub fn get_representative_token(&self) -> Token {
        match self {
            Token::Ident(_) => Token::Ident("".to_owned()),
            Token::Int(_) => Token::Int(0),
            _ => self.to_owned(),
        }
    }
}
