use super::ast::{FuncType, RecGroup, Subtype, ValueType};
use super::choices::GenerationError;
use super::natural::{self, Natural};
use super::sequence::{self, Sequence};

struct Comparison {
    left: Natural,
    right: Natural,
    equal: bool,
}

fn same_natural(left: &Natural, right: &Natural) -> bool {
    matches!(natural::difference(left, right), Some(Natural::Zero))
}

fn completed(comparisons: &Sequence<Comparison>, left: &Natural, right: &Natural) -> Option<bool> {
    match comparisons {
        Sequence::Empty => None,
        Sequence::Cons(cell) => {
            if same_natural(&cell.0.left, left) && same_natural(&cell.0.right, right) {
                Some(cell.0.equal)
            } else {
                completed(&cell.1, left, right)
            }
        }
    }
}

fn containing_group(groups: &Sequence<RecGroup>, index: Natural)
    -> Result<(&RecGroup, Natural), GenerationError>
{
    match groups {
        Sequence::Empty => Err(GenerationError::InternalInvariant),
        Sequence::Cons(cell) => {
            match natural::difference(&index, &sequence::length(&cell.0.members)) {
                None => Ok((&cell.0, index)),
                Some(rest) => containing_group(&cell.1, rest),
            }
        }
    }
}

/// In-group references roll to relative recursive variables; previous references close.
fn recursive_index(index: &Natural, base: &Natural, width: &Natural) -> Option<Natural> {
    match natural::difference(index, base) {
        None => None,
        Some(relative) => match natural::difference(&relative, width) {
            None => Some(relative),
            Some(_) => None,
        },
    }
}

fn closed_index(groups: &Sequence<RecGroup>, left: &Natural, left_base: &Natural, left_width: &Natural,
    right: &Natural, right_base: &Natural, right_width: &Natural, comparisons: Sequence<Comparison>)
    -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    match (recursive_index(left, left_base, left_width), recursive_index(right, right_base, right_width)) {
        (Some(left), Some(right)) => Ok((same_natural(&left, &right), comparisons)),
        (None, None) => compare_definition(groups, left, right, comparisons),
        _ => Ok((false, comparisons)),
    }
}

fn closed_values(groups: &Sequence<RecGroup>, left: &Sequence<ValueType>, left_base: &Natural, left_width: &Natural,
    right: &Sequence<ValueType>, right_base: &Natural, right_width: &Natural, comparisons: Sequence<Comparison>)
    -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    match (left, right) {
        (Sequence::Empty, Sequence::Empty) => Ok((true, comparisons)),
        (Sequence::Cons(left), Sequence::Cons(right)) => {
            let (equal, comparisons): (bool, Sequence<Comparison>) = match (&left.0, &right.0) {
                (ValueType::I32, ValueType::I32) | (ValueType::I64, ValueType::I64) => (true, comparisons),
                (ValueType::Ref(left_null, left_index), ValueType::Ref(right_null, right_index)) => {
                    if *left_null == *right_null {
                        closed_index(groups, left_index, left_base, left_width,
                            right_index, right_base, right_width, comparisons)?
                    } else {
                        (false, comparisons)
                    }
                }
                _ => (false, comparisons),
            };
            if equal {
                closed_values(groups, &left.1, left_base, left_width, &right.1, right_base, right_width, comparisons)
            } else {
                Ok((false, comparisons))
            }
        }
        _ => Ok((false, comparisons)),
    }
}

fn closed_signature(groups: &Sequence<RecGroup>, left: &FuncType, left_base: &Natural, left_width: &Natural,
    right: &FuncType, right_base: &Natural, right_width: &Natural, comparisons: Sequence<Comparison>)
    -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    let (equal, comparisons): (bool, Sequence<Comparison>) = closed_values(groups, &left.parameters,
        left_base, left_width, &right.parameters, right_base, right_width, comparisons)?;
    if equal {
        closed_values(groups, &left.results, left_base, left_width, &right.results, right_base, right_width, comparisons)
    } else {
        Ok((false, comparisons))
    }
}

fn closed_parent(groups: &Sequence<RecGroup>, left: &Option<Natural>, left_base: &Natural, left_width: &Natural,
    right: &Option<Natural>, right_base: &Natural, right_width: &Natural, comparisons: Sequence<Comparison>)
    -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    match (left, right) {
        (None, None) => Ok((true, comparisons)),
        (Some(left), Some(right)) => closed_index(groups, left, left_base, left_width,
            right, right_base, right_width, comparisons),
        _ => Ok((false, comparisons)),
    }
}

fn closed_members(groups: &Sequence<RecGroup>, left: &Sequence<Subtype>, left_base: &Natural, left_width: &Natural,
    right: &Sequence<Subtype>, right_base: &Natural, right_width: &Natural, comparisons: Sequence<Comparison>)
    -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    match (left, right) {
        (Sequence::Empty, Sequence::Empty) => Ok((true, comparisons)),
        (Sequence::Cons(left), Sequence::Cons(right)) => {
            if !(left.0.finality == right.0.finality) {
                return Ok((false, comparisons));
            }
            let (parent_equal, comparisons): (bool, Sequence<Comparison>) = closed_parent(groups,
                &left.0.parent, left_base, left_width, &right.0.parent, right_base, right_width, comparisons)?;
            if !parent_equal {
                return Ok((false, comparisons));
            }
            let (signature_equal, comparisons): (bool, Sequence<Comparison>) = closed_signature(groups,
                &left.0.signature, left_base, left_width, &right.0.signature, right_base, right_width, comparisons)?;
            if signature_equal {
                closed_members(groups, &left.1, left_base, left_width, &right.1, right_base, right_width, comparisons)
            } else {
                Ok((false, comparisons))
            }
        }
        _ => Ok((false, comparisons)),
    }
}

/// Cache only completed comparisons in this immutable group context, never pending pairs.
fn compare_definition(groups: &Sequence<RecGroup>, left: &Natural, right: &Natural,
    comparisons: Sequence<Comparison>) -> Result<(bool, Sequence<Comparison>), GenerationError>
{
    match completed(&comparisons, left, right) {
        Some(equal) => Ok((equal, comparisons)),
        None => {
            let (left_group, left_position): (&RecGroup, Natural) = containing_group(groups, natural::copy(left))?;
            let (right_group, right_position): (&RecGroup, Natural) = containing_group(groups, natural::copy(right))?;
            if !same_natural(&left_position, &right_position) {
                return Ok((false, comparisons));
            }
            let left_base: Natural = super::subtract(left, &left_position)?;
            let right_base: Natural = super::subtract(right, &right_position)?;
            let (equal, comparisons): (bool, Sequence<Comparison>) = closed_members(groups,
                &left_group.members, &left_base, &sequence::length(&left_group.members),
                &right_group.members, &right_base, &sequence::length(&right_group.members), comparisons)?;
            Ok((equal, sequence::cons(Comparison { left: natural::copy(left), right: natural::copy(right), equal }, comparisons)))
        }
    }
}

/// Definition identity includes the entire closed recursive group and member position.
pub fn same_definition(groups: &Sequence<RecGroup>, left: &Natural, right: &Natural) -> Result<bool, GenerationError> {
    let (equal, _): (bool, Sequence<Comparison>) = compare_definition(groups, left, right, Sequence::Empty)?;
    Ok(equal)
}

/// Body references resolve static indices to closed definitions, never to recursive atoms.
pub fn same_value(groups: &Sequence<RecGroup>, left: &ValueType, right: &ValueType) -> Result<bool, GenerationError> {
    match (left, right) {
        (ValueType::I32, ValueType::I32) | (ValueType::I64, ValueType::I64) => Ok(true),
        (ValueType::Ref(left_null, left_index), ValueType::Ref(right_null, right_index)) => {
            if *left_null == *right_null {
                same_definition(groups, left_index, right_index)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}
