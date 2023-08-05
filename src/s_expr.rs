use crate::ast::Def;
use crate::ast::Node;
use crate::r#type::Type;

#[derive(Debug)]
pub(crate) enum SExpr<'a> {
    A(SA<'a>),
    V(SV<'a>),
}

// S-Atom
#[derive(Debug)]
pub(crate) struct SA<'a> {
    val: &'a str,
    type_: Option<Type>,
}

// S-Vector (list)
#[derive(Debug)]
pub(crate) struct SV<'a> {
    vec: Vec<SExpr<'a>>,
    // Question: can we remove that type? Answer: No, when converting from AST, this is the return
    // type of a function, operator or lambda.
    type_: Option<Type>,
}

impl<'a> std::fmt::Display for SA<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)?;
        if let Some(type_) = &self.type_ {
            write!(f, " :: {type_}")?;
        }
        Ok(())
    }
}

impl<'a> std::fmt::Display for SV<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let separator = " ";
        write!(f, "(")?;
        if let Some(first) = &self.vec.first() {
            write!(f, "{first}")?;
        }
        for e in self.vec.iter().skip(1) {
            write!(f, "{separator}{e}")?;
        }
        write!(f, ")")?;
        if let Some(type_) = &self.type_ {
            write!(f, " :: {type_}")?;
        }
        Ok(())
    }
}

impl<'a> std::fmt::Display for SExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExpr::A(a) => {
                write!(f, "{a}")
            }
            SExpr::V(v) => {
                write!(f, "{v}")
            }
        }
    }
}

impl<'a> From<&'a Def> for SExpr<'a> {
    fn from(value: &'a Def) -> Self {
        SExpr::V(SV {
            vec: vec![
                SExpr::A(SA {
                    val: "def",
                    type_: None,
                }),
                SExpr::A(SA {
                    val: &value.token.literal,
                    type_: None,
                }),
                (&value.node).into(),
            ],
            type_: None,
        })
    }
}

impl<'a> From<&'a Node> for SExpr<'a> {
    fn from(node: &'a Node) -> Self {
        match &node.details {
            crate::ast::Details::IntLiteral(_)
            | crate::ast::Details::BoolLiteral(_)
            | crate::ast::Details::Identifier => SExpr::A(SA {
                val: &node.token.literal,
                type_: node.eval_type.clone().map(Type::Var),
            }),
            crate::ast::Details::OpExpr => {
                let mut vec = Vec::<SExpr<'a>>::with_capacity(node.children.len() + 1);
                let op_expr_node = SExpr::A(SA {
                    val: &node.token.literal,
                    type_: None,
                });
                vec.push(op_expr_node);
                for arg in &node.children {
                    vec.push(arg.into());
                }
                SExpr::V(SV {
                    vec,
                    type_: node.eval_type.clone().map(Type::Var),
                })
            }
            crate::ast::Details::FnAppExpr(fn_app_expr) => {
                let mut vec = Vec::<SExpr<'a>>::with_capacity(node.children.len() + 1);
                let fn_app_node = SExpr::A(SA {
                    val: &node.token.literal,
                    type_: fn_app_expr.fn_type.clone().map(Type::Var),
                });
                vec.push(fn_app_node);
                for arg in &node.children {
                    vec.push(arg.into());
                }
                SExpr::V(SV {
                    vec,
                    type_: node.eval_type.clone().map(Type::Var),
                })
            }
            crate::ast::Details::IfExpr => SExpr::V(SV {
                vec: vec![
                    SExpr::A(SA {
                        val: "if",
                        type_: None,
                    }),
                    (&node.children[0]).into(),
                    (&node.children[1]).into(),
                    (&node.children[2]).into(),
                ],
                type_: node.eval_type.clone().map(Type::Var),
            }),
            crate::ast::Details::LambdaExpr(lambda_expr) => {
                let mut arg_vec = Vec::with_capacity(node.children.len());
                for arg in node.children.iter().take(node.children.len() - 1) {
                    arg_vec.push(arg.into());
                }
                let vec = vec![
                    SExpr::A(SA {
                        val: "lambda",
                        type_: lambda_expr.fn_type.clone().map(Type::Var),
                    }),
                    SExpr::V(SV {
                        vec: arg_vec,
                        // This is the arg vec, it does not need a type.
                        type_: None,
                    }),
                    (node.children.last().expect("logic error")).into(),
                ];
                SExpr::V(SV {
                    vec,
                    type_: node.eval_type.clone().map(Type::Var),
                })
            }
        }
    }
}
