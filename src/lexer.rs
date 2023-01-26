use std::collections::VecDeque;

use crate::token::Token;

pub struct Lexer {
    input: VecDeque<char>,
}

impl Lexer {
    fn new(input: &str) -> Lexer {
        Lexer {
            input: input.to_string().chars().collect(),
        }
    }

    fn next_token(&mut self) -> Token {
        let input = &mut self.input;
        // remove whitespace.
        while !input.is_empty() && input.front().unwrap().is_whitespace() {
            input.pop_front();
        }
        if input.is_empty() {
            return Token::EOF;
        }
        let ch = input.pop_front().unwrap();
        let token = match ch {
            '=' => Token::ASSIGN,
            '+' => Token::PLUS,
            '-' => Token::MINUS,
            '!' => Token::BANG,
            '*' => Token::ASTERISK,
            '/' => Token::SLASH,
            '>' => Token::GT,
            '<' => Token::LT,
            '(' => Token::LPAREN,
            ')' => Token::RPAREN,
            '{' => Token::LBRACE,
            '}' => Token::RBRACE,
            ',' => Token::COMMA,
            ';' => Token::SEMICOLON,
            _ => Token::ILLEGAL,
        };
        if token != Token::ILLEGAL {
            return token;
        }
        // Token can be a multi-char type.
        let mut str = ch.to_string();
        if ch.is_digit(10) {
            while !input.is_empty() && input.front().unwrap().is_digit(10) {
                str.push(input.pop_front().unwrap());
            }
            return Token::INT(str.parse().unwrap());
        }
        if Lexer::is_valid_identifier_char(&ch) {
            while !input.is_empty() && Lexer::is_valid_identifier_char(input.front().unwrap()) {
                str.push(input.pop_front().unwrap());
            }
            match str.as_str() {
                "fn" => return Token::FUNCTION,
                "let" => return Token::LET,
                _ => return Token::IDENT(str),
            }
        }

        token
    }

    fn is_valid_identifier_char(ch: &char) -> bool {
        return ch.is_alphabetic() || *ch == '_';
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_token() {
        let input = r#"let five = 5;
let ten = 10;
let add = fn(x, y) {
  x + y;
};
let result = add(five, ten);
!-/*5;
5 < 10 > 5;
"#;

        let tests = [
            Token::LET,
            Token::IDENT(String::from("five")),
            Token::ASSIGN,
            Token::INT(5),
            Token::SEMICOLON,
            Token::LET,
            Token::IDENT("ten".to_string()),
            Token::ASSIGN,
            Token::INT(10),
            Token::SEMICOLON,
            Token::LET,
            Token::IDENT("add".to_string()),
            Token::ASSIGN,
            Token::FUNCTION,
            Token::LPAREN,
            Token::IDENT("x".to_string()),
            Token::COMMA,
            Token::IDENT("y".to_string()),
            Token::RPAREN,
            Token::LBRACE,
            Token::IDENT("x".to_string()),
            Token::PLUS,
            Token::IDENT("y".to_string()),
            Token::SEMICOLON,
            Token::RBRACE,
            Token::SEMICOLON,
            Token::LET,
            Token::IDENT("result".to_string()),
            Token::ASSIGN,
            Token::IDENT("add".to_string()),
            Token::LPAREN,
            Token::IDENT("five".to_string()),
            Token::COMMA,
            Token::IDENT("ten".to_string()),
            Token::RPAREN,
            Token::SEMICOLON,
            Token::BANG,
            Token::MINUS,
            Token::SLASH,
            Token::ASTERISK,
            Token::INT(5),
            Token::SEMICOLON,
            Token::INT(5),
            Token::LT,
            Token::INT(10),
            Token::GT,
            Token::INT(5),
            Token::SEMICOLON,
            Token::EOF,
        ];

        let mut l = Lexer::new(input);

        for tc in tests.iter() {
            assert_eq!(l.next_token(), *tc);
        }
    }
}
