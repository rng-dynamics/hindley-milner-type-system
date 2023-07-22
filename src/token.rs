pub(crate) type Position = usize;

#[derive(Clone, Copy, Debug, PartialEq, std::cmp::Eq, std::hash::Hash)]
pub(crate) enum TokenType {
    Illegal,
    Eof,

    Ident,
    Int,
    String,

    Assign,
    Plus,
    Hyphen,
    Asterisk,

    LParan,
    RParan,

    Comma,
    Dot,
    Bang,

    Lambda,
    If,
    Then,
    Else,
    True,
    False,

    Eq,
    NotEq,
    LtEq,
    GtEq,
}

#[derive(Clone, Debug, PartialEq, std::cmp::Eq, std::hash::Hash)]
pub(crate) struct Token {
    pub type_: TokenType,
    pub literal: String,
    pub position: Position,
}
