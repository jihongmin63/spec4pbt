#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
    Int,
    Boolean,
}

pub enum Expr {
    Int(u8),
    Bool(bool),
    Var(usize),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(ValueType, Box<Expr>, Box<Expr>),
}

