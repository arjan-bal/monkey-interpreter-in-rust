use std::{collections::VecDeque, path::Iter};

use crate::token::Token;

pub struct Lexer {
    input: VecDeque<char>,
    finished: bool,
}

impl Lexer {
    pub fn new(input: &str) -> Lexer {
        Lexer {
            input: input.to_string().chars().collect(),
            finished: false,
        }
    }

    fn get_one_char_token(ch: char) -> Option<Token> {
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
            _ => return None,
        };
        Some(token)
    }

    fn get_two_character_tokens(s: &str) -> Option<Token> {
        let token = match s {
            "==" => Token::EQ,
            "!=" => Token::NOT_EQ,
            _ => return None,
        };
        Some(token)
    }

    fn next_token(&mut self) -> Token {
        let input = &mut self.input;
        // remove whitespace.
        while !input.is_empty() && input.front().unwrap().is_whitespace() {
            input.pop_front();
        }

        if input.is_empty() {
            self.finished = true;
            return Token::EOF;
        }

        if input.len() >= 2 {
            if let Some(token) =
                Lexer::get_two_character_tokens(&String::from_iter(input.iter().take(2)))
            {
                input.pop_front().unwrap();
                input.pop_front().unwrap();
                return token;
            }
        }

        if let Some(token) = Lexer::get_one_char_token(input[0]) {
            input.pop_front().unwrap();
            return token;
        }

        // Token can be a multi-char type.
        let ch = input.pop_front().unwrap();
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
            let token = match str.as_str() {
                "fn" => Token::FUNCTION,
                "let" => Token::LET,
                "if" => Token::IF,
                "else" => Token::ELSE,
                "return" => Token::RETURN,
                "true" => Token::TRUE,
                "false" => Token::FALSE,
                _ => Token::IDENT(str),
            };
            return token;
        }

        Token::ILLEGAL
    }

    fn is_valid_identifier_char(ch: &char) -> bool {
        return ch.is_alphabetic() || *ch == '_';
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        Some(self.next_token())
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
if (5 < 10) {
  return true;
} else {
  return false;
}
10 == 10;
10 != 9;
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
            Token::IF,
            Token::LPAREN,
            Token::INT(5),
            Token::LT,
            Token::INT(10),
            Token::RPAREN,
            Token::LBRACE,
            Token::RETURN,
            Token::TRUE,
            Token::SEMICOLON,
            Token::RBRACE,
            Token::ELSE,
            Token::LBRACE,
            Token::RETURN,
            Token::FALSE,
            Token::SEMICOLON,
            Token::RBRACE,
            Token::INT(10),
            Token::EQ,
            Token::INT(10),
            Token::SEMICOLON,
            Token::INT(10),
            Token::NOT_EQ,
            Token::INT(9),
            Token::SEMICOLON,
            Token::EOF,
        ];

        let mut l = Lexer::new(input);

        for tc in tests.iter() {
            assert_eq!(l.next_token(), *tc);
        }
    }
}
