use regex::Regex;
use std::collections::HashMap;

pub(crate) use crate::token::*;

const ASSIGN: char = '=';
const PLUS: char = '+';
const BANG: char = '!';
const L_PARAN: char = '(';
const R_PARAN: char = ')';
const COMMA: char = ',';
const DOT: char = '.';
const SPACE: char = ' ';
const TAB: char = '\t';
const CR: char = '\r';
const LF: char = '\n';
const DOUBLE_QUOTE: char = '"';

pub(crate) struct LexerState<'a> {
    remaining_input: &'a str,
    position: usize,
}

impl<'a> LexerState<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            remaining_input: input,
            position: 0,
        }
    }

    fn advance(&mut self, cnt: usize) {
        let cnt = std::cmp::min(cnt, self.remaining_input.len());
        self.remaining_input = &self.remaining_input[cnt..];
        self.position += cnt;
    }

    fn skip_whitespace(&mut self) {
        while self.remaining_input.starts_with(char::is_whitespace) {
            self.advance(1);
        }
    }

    fn curr_str(&self) -> Option<&str> {
        if self.remaining_input.is_empty() {
            None
        } else {
            Some(self.remaining_input)
        }
    }
}

#[derive(Clone)]
pub(crate) struct LexerConfig<'a> {
    one_char_rules: &'a HashMap<char, TokenType>,
    two_char_rules: &'a HashMap<[char; 2], TokenType>,
    keyword_rules: &'a Vec<(String, TokenType)>,
    ident_rule: &'a (Regex, TokenType),
    generic_rules: &'a Vec<(Regex, TokenType)>,
    is_skip_whitespace: bool,
}

impl<'a> LexerConfig<'a> {
    pub(crate) fn new(
        one_char_rules: &'a HashMap<char, TokenType>,
        two_char_rules: &'a HashMap<[char; 2], TokenType>,
        keyword_rules: &'a Vec<(String, TokenType)>,
        ident_rule: &'a (Regex, TokenType),
        generic_rules: &'a Vec<(Regex, TokenType)>,
    ) -> Self {
        // TODO: check that all the regexes start with a caret.
        Self {
            one_char_rules,
            two_char_rules,
            keyword_rules,
            ident_rule,
            generic_rules,
            is_skip_whitespace: true,
        }
    }
}

pub(crate) struct Lexer<'a> {
    config: LexerConfig<'a>,
}

impl<'a> Lexer<'a> {
    pub(crate) fn new(config: LexerConfig<'a>) -> Self {
        Self { config }
    }

    fn match_two_chars(&self, state: &LexerState<'_>, str: &str) -> Option<Token> {
        for (two_chs, token_type) in self.config.two_char_rules {
            if str.starts_with(&String::from_iter(two_chs)) {
                let token = Token {
                    type_: *token_type,
                    literal: String::from_iter(two_chs),
                    position: state.position,
                };
                return Some(token);
            }
        }
        None
    }

    fn match_one_char(&self, state: &LexerState<'_>, str: &str) -> Option<Token> {
        for (ch, token_type) in self.config.one_char_rules {
            if str.starts_with::<char>(*ch) {
                let token = Token {
                    type_: *token_type,
                    literal: ch.to_string(),
                    position: state.position,
                };
                return Some(token);
            }
        }
        None
    }

    fn match_keywords(&self, state: &LexerState<'_>, str: &str) -> Option<Token> {
        for (keyword, token_type) in self.config.keyword_rules {
            if str.starts_with(keyword) {
                let token = Token {
                    type_: *token_type,
                    literal: keyword.clone(),
                    position: state.position,
                };
                return Some(token);
            }
        }
        None
    }

    fn match_identifier(&self, state: &LexerState<'_>, str: &str) -> Option<Token> {
        if let Some(mat) = self.config.ident_rule.0.find(str) {
            let literal_len = mat.end();
            let token = Token {
                type_: self.config.ident_rule.1,
                literal: str[..literal_len].to_string(),
                position: state.position,
            };
            return Some(token);
        }
        None
    }

    fn match_generic_rule(&self, state: &LexerState<'_>, str: &str) -> Option<Token> {
        for (regex, token_type) in self.config.generic_rules {
            if let Some(mat) = regex.find(str) {
                let literal_len = mat.end();
                let token = Token {
                    type_: *token_type,
                    literal: str[..literal_len].to_string(),
                    position: state.position,
                };
                return Some(token);
            }
        }
        None
    }

    pub(crate) fn next_token(&self, state: &mut LexerState<'_>) -> Token {
        if self.config.is_skip_whitespace {
            state.skip_whitespace();
        }
        match state.curr_str() {
            None => Token {
                type_: TokenType::Eof,
                literal: String::new(),
                position: state.position,
            },
            Some(str) => {
                // 1. Try to match two characters.
                if let Some(token) = self.match_two_chars(state, str) {
                    state.advance(token.literal.len());
                    return token;
                }

                // 2. Try to match one character.
                if let Some(token) = self.match_one_char(state, str) {
                    state.advance(token.literal.len());
                    return token;
                }

                // 3. Try to match keywords.
                if let Some(token) = self.match_keywords(state, str) {
                    state.advance(token.literal.len());
                    return token;
                }

                // 4. Try to match an identifier.
                if let Some(token) = self.match_identifier(state, str) {
                    state.advance(token.literal.len());
                    return token;
                }

                // 5. Try remaining rules.
                if let Some(token) = self.match_generic_rule(state, str) {
                    state.advance(token.literal.len());
                    return token;
                }
                Token {
                    type_: TokenType::Illegal,
                    literal: state.remaining_input.to_string(),
                    position: state.position,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lazy_static! {
        static ref ONE_CHAR_RULES: HashMap<char, TokenType> = HashMap::from([
            (PLUS, TokenType::Plus),
            (ASSIGN, TokenType::Assign),
            (L_PARAN, TokenType::LParan),
            (R_PARAN, TokenType::RParan),
            (COMMA, TokenType::Comma),
            (DOT, TokenType::Dot),
            (BANG, TokenType::Bang),
        ]);
        static ref TWO_CHAR_RULES: HashMap<[char; 2], TokenType> = HashMap::from([
            ([ASSIGN, ASSIGN], TokenType::Eq),
            ([BANG, ASSIGN], TokenType::NotEq),
        ]);
        static ref KEYWORDS: Vec<(String, TokenType)> = vec![
            (String::from("true"), TokenType::True),
            (String::from("false"), TokenType::False),
            (String::from("lambda"), TokenType::Lambda),
            (String::from("if"), TokenType::If),
            (String::from("else"), TokenType::Else),
        ];
        static ref IDENTIFIER_RULE: (Regex, TokenType) =
            (Regex::new(r"^\p{L}+").unwrap(), TokenType::Ident);
        static ref GENERIC_RULES: Vec<(Regex, TokenType)> =
            vec![(Regex::new(r"^\d+").unwrap(), TokenType::Int),];
        static ref LEXER_CONFIG: LexerConfig<'static> = LexerConfig::new(
            &ONE_CHAR_RULES,
            &TWO_CHAR_RULES,
            &KEYWORDS,
            &IDENTIFIER_RULE,
            &GENERIC_RULES,
        );
    }

    #[test]
    fn test_input_1() {
        let input = "=+(,).";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Assign, "="),
            (TokenType::Plus, "+"),
            (TokenType::LParan, "("),
            (TokenType::Comma, ","),
            (TokenType::RParan, ")"),
            (TokenType::Dot, "."),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_2() {
        let input = "foo = lambda";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Ident, "foo"),
            (TokenType::Assign, "="),
            (TokenType::Lambda, "lambda"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_3() {
        let input = "foo = 25true false";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Ident, "foo"),
            (TokenType::Assign, "="),
            (TokenType::Int, "25"),
            (TokenType::True, "true"),
            (TokenType::False, "false"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_4() {
        let input = "foo =if true42else21";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Ident, "foo"),
            (TokenType::Assign, "="),
            (TokenType::If, "if"),
            (TokenType::True, "true"),
            (TokenType::Int, "42"),
            (TokenType::Else, "else"),
            (TokenType::Int, "21"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_5() {
        let input = "if 42==21 false else true";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::If, "if"),
            (TokenType::Int, "42"),
            (TokenType::Eq, "=="),
            (TokenType::Int, "21"),
            (TokenType::False, "false"),
            (TokenType::Else, "else"),
            (TokenType::True, "true"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_6() {
        let input = "42!=21 !false";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Int, "42"),
            (TokenType::NotEq, "!="),
            (TokenType::Int, "21"),
            (TokenType::Bang, "!"),
            (TokenType::False, "false"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }

    #[test]
    fn test_input_7() {
        let input = "= ==, true != false";
        let expected: Vec<(TokenType, &str)> = vec![
            (TokenType::Assign, "="),
            (TokenType::Eq, "=="),
            (TokenType::Comma, ","),
            (TokenType::True, "true"),
            (TokenType::NotEq, "!="),
            (TokenType::False, "false"),
            (TokenType::Eof, ""),
        ];

        let lexer = Lexer::new(LEXER_CONFIG.clone());

        let mut state = LexerState::new(input);

        for (expected_type, expected_literal) in expected {
            let token = lexer.next_token(&mut state);

            assert_eq!(token.type_, expected_type);
            assert_eq!(token.literal, expected_literal);
        }
    }
}
