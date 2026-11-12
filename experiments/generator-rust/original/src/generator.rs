use crate::ast::{Expr, ValueType};

/// SplitMix64 returns a random word and the next state without mutating its input.
fn next_random(state: u64) -> (u64, u64) {
    let next_state: u64 = state.wrapping_add(0x9e3779b97f4a7c15);
    let mixed: u64 = (next_state ^ (next_state >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let mixed: u64 = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d049bb133111eb);
    (mixed ^ (mixed >> 31), next_state)
}

fn choose(bound: usize, state: u64) -> (usize, u64) {
    let (word, next_state): (u64, u64) = next_random(state);
    ((word % bound as u64) as usize, next_state)
}

fn literal(value_type: ValueType, state: u64) -> (Expr, u64) {
    match value_type {
        ValueType::Int => {
            let (value, next_state): (usize, u64) = choose(256, state);
            (Expr::Int(value as u8), next_state)
        }
        ValueType::Bool => {
            let (value, next_state): (usize, u64) = choose(2, state);
            (Expr::Bool(value != 0), next_state)
        }
    }
}

fn leaf(value_type: ValueType, context: &[ValueType], state: u64) -> (Expr, u64) {
    let matches: usize = context.iter().filter(|entry| **entry == value_type).count();
    if matches == 0 {
        return literal(value_type, state);
    }
    let (family, state): (usize, u64) = choose(2, state);
    if family == 0 {
        return literal(value_type, state);
    }
    let (selected, state): (usize, u64) = choose(matches, state);
    let (index, _): (usize, &ValueType) = context
        .iter()
        .enumerate()
        .filter(|(_, entry)| **entry == value_type)
        .nth(selected)
        .expect("selected variable rank must be below the matching context count");
    (Expr::Var(index), state)
}

fn unary(value_type: ValueType, nodes: usize, context: &[ValueType], state: u64) -> (Expr, u64) {
    let (child, state): (Expr, u64) = generate(value_type, nodes - 1, context, state);
    let expr: Expr = match value_type {
        ValueType::Int => Expr::Neg(Box::new(child)),
        ValueType::Bool => Expr::Not(Box::new(child)),
    };
    (expr, state)
}

fn binary(value_type: ValueType, nodes: usize, context: &[ValueType], state: u64) -> (Expr, u64) {
    let (cut, state): (usize, u64) = choose(nodes - 2, state);
    let left_nodes: usize = cut + 1;
    let (left, state): (Expr, u64) = generate(ValueType::Int, left_nodes, context, state);
    let (right, state): (Expr, u64) =
        generate(ValueType::Int, nodes - 1 - left_nodes, context, state);
    let expr: Expr = match value_type {
        ValueType::Int => Expr::Add(Box::new(left), Box::new(right)),
        ValueType::Bool => Expr::Eq(Box::new(left), Box::new(right)),
    };
    (expr, state)
}

fn let_expr(value_type: ValueType, nodes: usize, context: &[ValueType], state: u64) -> (Expr, u64) {
    let (binder_choice, state): (usize, u64) = choose(2, state);
    let binder: ValueType = if binder_choice == 0 { ValueType::Int } else { ValueType::Bool };
    let (cut, state): (usize, u64) = choose(nodes - 2, state);
    let rhs_nodes: usize = cut + 1;
    let (rhs, state): (Expr, u64) = generate(binder, rhs_nodes, context, state);
    let body_context: Vec<ValueType> = std::iter::once(binder)
        .chain(context.iter().copied())
        .collect();
    let (body, state): (Expr, u64) =
        generate(value_type, nodes - 1 - rhs_nodes, &body_context, state);
    (Expr::Let(binder, Box::new(rhs), Box::new(body)), state)
}

fn if_expr(value_type: ValueType, nodes: usize, context: &[ValueType], state: u64) -> (Expr, u64) {
    let (first_cut, state): (usize, u64) = choose(nodes - 3, state);
    let condition_nodes: usize = first_cut + 1;
    let (second_cut, state): (usize, u64) = choose(nodes - 2 - condition_nodes, state);
    let yes_nodes: usize = second_cut + 1;
    let no_nodes: usize = nodes - 1 - condition_nodes - yes_nodes;
    let (condition, state): (Expr, u64) = generate(ValueType::Bool, condition_nodes, context, state);
    let (yes, state): (Expr, u64) = generate(value_type, yes_nodes, context, state);
    let (no, state): (Expr, u64) = generate(value_type, no_nodes, context, state);
    (Expr::If(Box::new(condition), Box::new(yes), Box::new(no)), state)
}

/// Construct exactly `nodes` well-typed nodes with every feasible family available.
pub fn generate(value_type: ValueType, nodes: usize, context: &[ValueType], state: u64) -> (Expr, u64) {
    if nodes == 1 {
        return leaf(value_type, context, state);
    }
    let family_count: usize = match nodes {
        2 => 1,
        3 => 3,
        _ => 4,
    };
    let (family, state): (usize, u64) = choose(family_count, state);
    match family {
        0 => unary(value_type, nodes, context, state),
        1 => binary(value_type, nodes, context, state),
        2 => let_expr(value_type, nodes, context, state),
        3 => if_expr(value_type, nodes, context, state),
        _ => unreachable!("constructor family must be below the feasible family count"),
    }
}
