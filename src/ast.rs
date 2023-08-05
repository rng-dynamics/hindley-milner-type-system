use crate::token::Token;
use crate::type_var::TypeVar;
use std::cmp::Eq;
use std::hash::Hash;

// A definition, Def, has a name and an expression represented as AST node.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Def {
    pub token: Token,
    pub node: Node,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Node {
    pub token: Token,
    // No matter what the node represents the type of the node should be equal to the type of the
    // result obtained by evaluating the node. That is, one can always know what to get after
    // evaluation by just looking at this field. This make the type-inference sane.
    pub eval_type: Option<TypeVar>,
    pub details: Details,
    pub children: Vec<Node>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Details {
    IntLiteral(IntLiteral),

    BoolLiteral(BoolLiteral),

    Identifier,

    // For OpExpr the operator is stored in the token of the node. The operands are stored as
    // children.
    OpExpr,

    // For FnAppExpr, the function identifier is stored in "this node". The type in "this node" is
    // the type which is obtained when one evaluates this node (a.k.a. the return type). The function
    // type (in contrast to the return type) is stored in the nested structure. The children are the
    // function arguments.
    FnAppExpr(FnType),

    // For IfExpr the first child is the conditional, the second node is the then expression and
    // the third child is the else expression.
    IfExpr,

    // For LambdaExpr the first n children are the arguments and the last child is the lambda body.
    LambdaExpr(FnType),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct IntLiteral {
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BoolLiteral {
    pub value: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FnType {
    pub fn_type: Option<TypeVar>,
}
