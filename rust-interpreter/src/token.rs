use std::fmt::{self, Display};

#[derive(PartialEq, Clone, Eq, Hash, Debug)]
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

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let res = match self {
            Token::Illegal => "Illegal",
            Token::EOF => "EOF",
            Token::Ident(x) => x,
            Token::Int(x) => {
                s = x.to_string();
                s.as_str()
            }
            Token::True => "true",
            Token::False => "false",
            Token::Assign => "=",
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Bang => "!",
            Token::Asterisk => "*",
            Token::Slash => "/",
            Token::EQ => "==",
            Token::NotEq => "!=",
            Token::LT => "<",
            Token::GT => ">",
            Token::Comma => ",",
            Token::Semicolon => ";",
            Token::LParen => "(",
            Token::RParen => ")",
            Token::RBrace => "{",
            Token::LBrace => "}",
            Token::Function => "fn",
            Token::Let => "let",
            Token::If => "if",
            Token::Else => "else",
            Token::Return => "return",
        };
        write!(f, "{}", res)
    }
}
