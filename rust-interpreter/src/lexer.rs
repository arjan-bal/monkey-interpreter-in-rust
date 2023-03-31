use std::collections::VecDeque;

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
            '=' => Token::Assign,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '!' => Token::Bang,
            '*' => Token::Asterisk,
            '/' => Token::Slash,
            '>' => Token::GT,
            '<' => Token::LT,
            '(' => Token::LParen,
            ')' => Token::RParen,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ',' => Token::Comma,
            ';' => Token::Semicolon,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            ':' => Token::Colon,
            _ => return None,
        };
        Some(token)
    }

    fn get_two_character_tokens(s: &str) -> Option<Token> {
        let token = match s {
            "==" => Token::EQ,
            "!=" => Token::NotEq,
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
            return Token::Int(str.parse().unwrap());
        }
        if Lexer::is_valid_identifier_char(&ch) {
            while !input.is_empty() && Lexer::is_valid_identifier_char(input.front().unwrap()) {
                str.push(input.pop_front().unwrap());
            }
            let token = match str.as_str() {
                "fn" => Token::Function,
                "let" => Token::Let,
                "if" => Token::If,
                "else" => Token::Else,
                "return" => Token::Return,
                "true" => Token::True,
                "false" => Token::False,
                _ => Token::Ident(str),
            };
            return token;
        }

        // check for string.
        if ch == '"' {
            str = String::new();
            while input.front() != Some(&'"') {
                str.push(input.pop_front().unwrap());
            }
            if input.front() != Some(&'"') {
                return Token::Illegal;
            }
            input.pop_front().unwrap();
            return Token::String(str);
        }

        Token::Illegal
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
"foobar"
"foo bar"
[1, 2];
{a: 10};
"#;

        let tests = [
            Token::Let,
            Token::Ident(String::from("five")),
            Token::Assign,
            Token::Int(5),
            Token::Semicolon,
            Token::Let,
            Token::Ident("ten".to_string()),
            Token::Assign,
            Token::Int(10),
            Token::Semicolon,
            Token::Let,
            Token::Ident("add".to_string()),
            Token::Assign,
            Token::Function,
            Token::LParen,
            Token::Ident("x".to_string()),
            Token::Comma,
            Token::Ident("y".to_string()),
            Token::RParen,
            Token::LBrace,
            Token::Ident("x".to_string()),
            Token::Plus,
            Token::Ident("y".to_string()),
            Token::Semicolon,
            Token::RBrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident("result".to_string()),
            Token::Assign,
            Token::Ident("add".to_string()),
            Token::LParen,
            Token::Ident("five".to_string()),
            Token::Comma,
            Token::Ident("ten".to_string()),
            Token::RParen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Int(5),
            Token::Semicolon,
            Token::Int(5),
            Token::LT,
            Token::Int(10),
            Token::GT,
            Token::Int(5),
            Token::Semicolon,
            Token::If,
            Token::LParen,
            Token::Int(5),
            Token::LT,
            Token::Int(10),
            Token::RParen,
            Token::LBrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::RBrace,
            Token::Else,
            Token::LBrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::RBrace,
            Token::Int(10),
            Token::EQ,
            Token::Int(10),
            Token::Semicolon,
            Token::Int(10),
            Token::NotEq,
            Token::Int(9),
            Token::Semicolon,
            Token::String("foobar".to_owned()),
            Token::String("foo bar".to_owned()),
            Token::LBracket,
            Token::Int(1),
            Token::Comma,
            Token::Int(2),
            Token::RBracket,
            Token::Semicolon,
            Token::LBrace,
            Token::Ident("a".to_owned()),
            Token::Colon,
            Token::Int(10),
            Token::RBrace,
            Token::Semicolon,
            Token::EOF,
        ];

        let mut l = Lexer::new(input);

        for tc in tests.iter() {
            assert_eq!(l.next_token(), *tc);
        }
    }
}
