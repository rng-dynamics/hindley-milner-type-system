use std::collections::HashMap;

use regex::Regex;

use crate::{
    ast::*,
    lexer::{Lexer, LexerConfig, LexerState, TokenType},
    token::Token,
};

lazy_static! {
    static ref ONE_CHAR_RULES: HashMap<char, TokenType> = HashMap::from([
        ('+', TokenType::Plus),
        ('-', TokenType::Hyphen),
        ('*', TokenType::Asterisk),
        ('=', TokenType::Assign),
        ('(', TokenType::LParan),
        (')', TokenType::RParan),
        (',', TokenType::Comma),
        ('.', TokenType::Dot),
        ('!', TokenType::Bang),
    ]);

    static ref TWO_CHAR_RULES: HashMap<[char; 2], TokenType> = HashMap::from([
        (['=', '='], TokenType::Eq),
        (['!', '='], TokenType::NotEq),
        (['<', '='], TokenType::LtEq),
        (['>', '='], TokenType::GtEq),
    ]);

    static ref KEYWORD_RULES: Vec<(String, TokenType)> = vec![
        (String::from("true"), TokenType::True),
        (String::from("false"), TokenType::False),
        (String::from("lambda"), TokenType::Lambda),
        (String::from("if"), TokenType::If),
        (String::from("then"), TokenType::Then),
        (String::from("else"), TokenType::Else),
    ];

    static ref IDENT_RULE: (Regex, TokenType) =
        (Regex::new(r"^\p{L}[\p{L}\d\-_]*").unwrap(), TokenType::Ident);

    static ref GENERIC_RULES: Vec<(Regex, TokenType)> =
        vec![(Regex::new(r"^\d+").unwrap(), TokenType::Int)];

    static ref LEXER_CONFIG: LexerConfig<'static> = LexerConfig::new(
        &ONE_CHAR_RULES,
        &TWO_CHAR_RULES,
        &KEYWORD_RULES,
        &IDENT_RULE,
        &GENERIC_RULES,
    );

    // Binding power in Pratt Parsing represented by u8. For asscoiativity add one. The
    // power 0 is reserved for the end of the input.
    static ref INFIX_BINDING_POWER: HashMap<TokenType, (u8, u8)> =
        HashMap::from([
            (TokenType::Eq, (1, 2)),
            (TokenType::NotEq, (1, 2)),
            (TokenType::LtEq, (1, 2)),
            (TokenType::GtEq, (1, 2)),
            (TokenType::Plus, (3, 4)),
            (TokenType::Hyphen, (3, 4)),
            (TokenType::Asterisk, (5, 6))
    ]);

    // Binding power of prefix operators is also representd as a pair (the same as for
    // infix operators), but the first value is empty because it binds only to the right.
    static ref PREFIX_BINDING_POWER: HashMap<TokenType, ((), u8)> =
        HashMap::from([
            (TokenType::Hyphen, ((), 7))
    ]);
}

struct ParserCore<'a, 'b> {
    lexer: Lexer<'a>,
    lexer_state: LexerState<'b>,
    curr_token: Token,
    peek_token: Token,
}

impl<'a, 'b> ParserCore<'a, 'b> {
    fn new(input: &'b str) -> Self {
        let lexer = Lexer::new(LEXER_CONFIG.clone());
        let mut lexer_state = LexerState::new(input);
        let curr_token = lexer.next_token(&mut lexer_state);
        let peek_token = lexer.next_token(&mut lexer_state);

        Self {
            lexer,
            lexer_state,
            curr_token,
            peek_token,
        }
    }

    fn next_token(&mut self) {
        self.curr_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token(&mut self.lexer_state);
    }

    fn match_token_type(&mut self, requested_type: TokenType) -> Option<Token> {
        if self.curr_token.type_ == requested_type {
            let token = self.curr_token.clone();
            self.next_token();
            return Some(token);
        }
        None
    }
}

pub(crate) struct Parser<'a> {
    infix_binding_power: &'a HashMap<TokenType, (u8, u8)>,
    prefix_binding_power: &'a HashMap<TokenType, ((), u8)>,
}

impl<'a> Parser<'a> {
    pub(crate) fn new() -> Self {
        Self {
            infix_binding_power: &INFIX_BINDING_POWER,
            prefix_binding_power: &PREFIX_BINDING_POWER,
        }
    }

    fn is_prefix_operator(&self, token: &Token) -> bool {
        self.prefix_binding_power.get(&token.type_).is_some()
    }

    fn is_infix_operator(&self, token: &Token) -> bool {
        self.infix_binding_power.get(&token.type_).is_some()
    }

    pub(crate) fn parse_def(&self, input: &str) -> Option<Def> {
        self.parse_def_aux(&mut ParserCore::new(input))
    }

    fn parse_def_aux(&self, core: &mut ParserCore<'_, '_>) -> Option<Def> {
        let mut idents: Vec<Token> = vec![];
        while let Some(ident) = core.match_token_type(TokenType::Ident) {
            idents.push(ident);
        }
        if idents.is_empty() {
            // error
            return None;
        }
        core.match_token_type(TokenType::Assign)?;

        if let Some(expr) = self.parse_expr(core) {
            let expr = if 1 == idents.len() {
                expr
            } else {
                let mut children = Vec::new();
                for ident in idents.iter().skip(1) {
                    children.push(Node {
                        token: ident.clone(),
                        eval_type: None,
                        children: vec![],
                        details: Details::Identifier,
                    });
                }
                children.push(expr);
                Node {
                    token: idents[0].clone(),
                    eval_type: None,
                    children,
                    details: Details::LambdaExpr(FnType { fn_type: None }),
                }
            };
            Some(Def {
                token: idents[0].clone(),
                node: expr,
            })
        } else {
            None
        }
    }

    fn parse_atom(&self, core: &mut ParserCore<'_, '_>) -> Option<Node> {
        let curr_token = core.curr_token.clone();
        match curr_token.type_ {
            TokenType::Int => {
                let value = curr_token.literal.parse::<u64>().expect("logic error");
                let int_literal = Node {
                    token: curr_token,
                    eval_type: None,
                    children: vec![],
                    details: Details::IntLiteral(IntLiteral { value }),
                };
                core.next_token();
                Some(int_literal)
            }
            TokenType::True | TokenType::False => {
                let value = curr_token.type_ == TokenType::True;
                let bool_literal = Node {
                    token: curr_token,
                    eval_type: None,
                    children: vec![],
                    details: Details::BoolLiteral(BoolLiteral { value }),
                };
                core.next_token();
                Some(bool_literal)
            }
            TokenType::Ident => {
                if core.peek_token.type_ == TokenType::LParan {
                    self.parse_fn_app(core)
                } else {
                    let identifier = Node {
                        token: curr_token,
                        eval_type: None,
                        children: vec![],
                        details: Details::Identifier,
                    };
                    core.next_token();
                    Some(identifier)
                }
            }
            _ => None,
        }
    }

    fn parse_fn_app(&self, core: &mut ParserCore<'_, '_>) -> Option<Node> {
        let fn_app_token = core.curr_token.clone();
        core.next_token();
        core.match_token_type(TokenType::LParan)?;
        let mut args = vec![];
        while let Some(statement) = self.parse_expr(core) {
            args.push(statement);
            let next_token_is_comma = core.match_token_type(TokenType::Comma).is_some();
            if !next_token_is_comma {
                break;
            }
        }
        core.match_token_type(TokenType::RParan)?;

        Some(Node {
            token: fn_app_token,
            eval_type: None,
            children: args,
            details: Details::FnAppExpr(FnType { fn_type: None }),
        })
    }

    fn parse_atom_or_paran_expr(&self, core: &mut ParserCore<'_, '_>) -> Option<Node> {
        if core.match_token_type(TokenType::LParan).is_some() {
            let node = self.parse_expr(core)?;
            core.match_token_type(TokenType::RParan)?;
            Some(node)
        } else {
            self.parse_atom(core)
        }
    }

    fn parse_expr(&self, core: &mut ParserCore<'_, '_>) -> Option<Node> {
        if let Some(if_token) = core.match_token_type(TokenType::If) {
            let if_expr = self.parse_expr(core)?;
            core.match_token_type(TokenType::Then)?;
            let then_expr = self.parse_expr(core)?;
            core.match_token_type(TokenType::Else)?;
            let else_expr = self.parse_expr(core)?;
            Some(Node {
                token: if_token,
                eval_type: None,
                children: vec![if_expr, then_expr, else_expr],
                details: Details::IfExpr,
            })
        } else {
            self.parse_op_expr_bp(core, 0)
        }
    }

    // Pratt Parsing of operator expressions using binding-power (bp).
    fn parse_op_expr_bp(&self, core: &mut ParserCore<'_, '_>, min_bp: u8) -> Option<Node> {
        let mut lhs = if self.is_prefix_operator(&core.curr_token) {
            // handle prefix operator
            let op_token = core.curr_token.clone();
            let bp = self.prefix_binding_power.get(&op_token.type_);
            let ((), r_bp) = bp.unwrap_or(&((), 0));
            core.next_token();
            let rhs = self.parse_op_expr_bp(core, *r_bp)?;
            Node {
                token: op_token,
                eval_type: None,
                details: Details::OpExpr,
                children: vec![rhs],
            }
        } else {
            self.parse_atom_or_paran_expr(core)?
        };

        // handle infix operators in a combination of loop and recursion (Pratt Parsing)
        loop {
            if !self.is_infix_operator(&core.curr_token) {
                break;
            }
            let op_token = core.curr_token.clone();

            let bp = self.infix_binding_power.get(&op_token.type_);
            let (l_bp, r_bp) = bp.unwrap_or(&(0, 0));
            if *l_bp < min_bp {
                break;
            }

            core.next_token();
            let rhs = self.parse_op_expr_bp(core, *r_bp)?;

            lhs = Node {
                token: op_token,
                eval_type: None,
                details: Details::OpExpr,
                children: vec![lhs, rhs],
            };
        }
        Some(lhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::s_expr::SExpr;

    use super::*;

    #[test]
    fn test_variable_integer_assignment() {
        let input = "varname = 25";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!("(def varname 25)", SExpr::from(&ast).to_string());
    }

    #[test]
    fn test_simple_function_definition() {
        let input = "funcname param = true";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def funcname (lambda (param) true))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_1() {
        let input = "minus p1 p2 = p1 - p2";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def minus (lambda (p1 p2) (- p1 p2)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_2() {
        let input = "sum-plus-4 p1 p2 = p1 + 4 + p2";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def sum-plus-4 (lambda (p1 p2) (+ (+ p1 4) p2)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_3() {
        let input = "func p1 p2 = ( p1 + 4 ) * p2";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (p1 p2) (* (+ p1 4) p2)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_4() {
        let input = "func p1 p2 = p1 + 4 * p2";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (p1 p2) (+ p1 (* 4 p2))))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_5() {
        let input = "func p1 p2 = p1 * 4 + p2";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (p1 p2) (+ (* p1 4) p2)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_6() {
        let input = "func p1 p2 = p1 + ( 4  * p2 )";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (p1 p2) (+ p1 (* 4 p2))))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_7() {
        let input = "inv p1 = -p1";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def inv (lambda (p1) (- p1)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_operator_expression_8() {
        let input = "func p1 p2 = p1 + ( (-4)  * -p2 )";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (p1 p2) (+ p1 (* (- 4) (- p2)))))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_fn_app() {
        let input = "fn1 = fn2(3)";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!("(def fn1 (fn2 3))", SExpr::from(&ast).to_string());
    }

    #[test]
    fn test_fn_app_2() {
        let input = "fn1 pa = fn2(false, pa)";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def fn1 (lambda (pa) (fn2 false pa)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_fn_app_3() {
        let input = "fn1 pa = fn2(false, fn3(pa))";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def fn1 (lambda (pa) (fn2 false (fn3 pa))))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_if_expr() {
        let input = "ee = if a then b else c";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!("(def ee (if a b c))", SExpr::from(&ast).to_string());
    }

    #[test]
    fn test_equal() {
        let input = "ee xx = xx == 1";
        let parser = Parser::new();

        let ast = parser.parse_def(input).unwrap();

        assert_eq!(
            "(def ee (lambda (xx) (== xx 1)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_if_expr_2() {
        let input = "func f1 f2 p3 = if f1(p3 + 1) then f2(p3) else 42";
        let ast = Parser::new().parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (f1 f2 p3) (if (f1 (+ p3 1)) (f2 p3) 42)))",
            SExpr::from(&ast).to_string()
        );
    }

    #[test]
    fn test_func() {
        let input = "func f1 x2 = f1(3) + f1(x2)";
        let ast = Parser::new().parse_def(input).unwrap();

        assert_eq!(
            "(def func (lambda (f1 x2) (+ (f1 3) (f1 x2))))",
            SExpr::from(&ast).to_string()
        );
    }
}
