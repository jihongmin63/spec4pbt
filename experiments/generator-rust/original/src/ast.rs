#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
    Int,
    Bool,
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

pub struct Inspection {
    pub nodes: u64,
    pub digest: u64,
}

pub fn type_name(value_type: ValueType) -> &'static str {
    match value_type {
        ValueType::Int => "int",
        ValueType::Bool => "bool",
    }
}

pub fn root_type(index: u64) -> ValueType {
    if index % 2 == 0 {
        ValueType::Int
    } else {
        ValueType::Bool
    }
}

pub fn fold_digest(accumulator: u64, value: u64) -> u64 {
    accumulator.wrapping_mul(1_000_003).wrapping_add(value)
}

fn inspect_node(tag: u64, payloads: &[u64], children: &[&Expr]) -> Inspection {
    let mut digest: u64 = tag;
    let mut nodes: u64 = 1;
    for payload in payloads {
        digest = fold_digest(digest, *payload);
    }
    for child in children {
        let inspected: Inspection = inspect(child);
        nodes += inspected.nodes;
        digest = fold_digest(digest, inspected.digest);
    }
    Inspection { nodes, digest }
}

pub fn inspect(expr: &Expr) -> Inspection {
    match expr {
        Expr::Int(value) => inspect_node(1, &[u64::from(*value)], &[]),
        Expr::Bool(value) => inspect_node(2, &[u64::from(*value)], &[]),
        Expr::Var(index) => inspect_node(3, &[*index as u64], &[]),
        Expr::Neg(child) => inspect_node(4, &[], &[child]),
        Expr::Not(child) => inspect_node(5, &[], &[child]),
        Expr::Add(left, right) => inspect_node(6, &[], &[left, right]),
        Expr::Eq(left, right) => inspect_node(7, &[], &[left, right]),
        Expr::If(condition, yes, no) => inspect_node(8, &[], &[condition, yes, no]),
        Expr::Let(binder, rhs, body) => inspect_node(
            9,
            &[u64::from(*binder == ValueType::Bool)],
            &[rhs, body],
        ),
    }
}

pub fn expression_json(expr: &Expr) -> String {
    match expr {
        Expr::Int(value) => format!("[\"int\",{value}]"),
        Expr::Bool(value) => format!("[\"bool\",{value}]"),
        Expr::Var(index) => format!("[\"var\",{index}]"),
        Expr::Neg(child) => format!("[\"neg\",{}]", expression_json(child)),
        Expr::Not(child) => format!("[\"not\",{}]", expression_json(child)),
        Expr::Add(left, right) => {
            format!("[\"add\",{},{}]", expression_json(left), expression_json(right))
        }
        Expr::Eq(left, right) => {
            format!("[\"eq\",{},{}]", expression_json(left), expression_json(right))
        }
        Expr::If(condition, yes, no) => format!(
            "[\"if\",{},{},{}]",
            expression_json(condition),
            expression_json(yes),
            expression_json(no),
        ),
        Expr::Let(binder, rhs, body) => format!(
            "[\"let\",\"{}\",{},{}]",
            type_name(*binder),
            expression_json(rhs),
            expression_json(body),
        ),
    }
}
