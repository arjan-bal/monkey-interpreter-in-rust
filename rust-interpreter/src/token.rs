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

    String(String),

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
    Colon,

    LParen,
    RParen,
    RBrace,
    LBrace,
    LBracket,
    RBracket,

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
            Token::String(_) => Token::String("".to_owned()),
            _ => self.to_owned(),
        }
    }

    /// Returns `true` if the token is [`Ident`].
    ///
    /// [`Ident`]: Token::Ident
    #[must_use]
    pub fn is_ident(&self) -> bool {
        matches!(self, Self::Ident(..))
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s;
        let res = match self {
            Token::Illegal => "Illegal",
            Token::EOF => "EOF",
            Token::Ident(x) => x,
            Token::Int(x) => {
                s = x.to_string();
                &s
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
            Token::LBracket => "[",
            Token::RBracket => "]",
            Token::Function => "fn",
            Token::Let => "let",
            Token::If => "if",
            Token::Else => "else",
            Token::Return => "return",
            Token::Colon => ":",
            Token::String(s) => s,
        };
        write!(f, "{}", res)
    }
}
