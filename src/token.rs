
#[derive(PartialEq, Debug)]
pub enum Token {
  ILLEGAL,
  EOF,

  // Identifiers + literals
  IDENT(String),
  INT(i64),

  // Operators
  ASSIGN,
  PLUS,
  MINUS,
  BANG,
  ASTERISK,
  SLASH,

  LT,
  GT,

  // Delimiters
  COMMA,
  SEMICOLON,

  LPAREN,
  RPAREN,
  RBRACE,
  LBRACE,

  // Keywords
  FUNCTION,
  LET,

}
