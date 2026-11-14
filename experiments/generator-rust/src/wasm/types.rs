use super::ast::{copy_signature, Finality, FuncType, Nullability, RecGroup, Subtype, ValueType};
use super::choices::{pick_natural, pick_word, Choices, GenerationError};
use super::natural::{self, Natural};
use super::sequence::{self, Sequence};
use super::Config;

struct Header {
    finality: Finality,
    parent: Option<Natural>,
}

fn reference(type_count: &Natural, choices: Choices) -> Result<(ValueType, Choices), GenerationError> {
    let (selected, choices): (u64, Choices) = pick_word(2, choices)?;
    let nullability: Nullability = if selected == 0 { Nullability::Nullable } else { Nullability::NonNull };
    let (index, choices): (Natural, Choices) = pick_natural(type_count, choices)?;
    Ok((ValueType::Ref(nullability, index), choices))
}

fn value(type_count: &Natural, choices: Choices) -> Result<(ValueType, Choices), GenerationError> {
    let bound: u64 = match type_count { Natural::Zero => 2, Natural::Positive(_) => 3 };
    let (selected, choices): (u64, Choices) = pick_word(bound, choices)?;
    match selected {
        0 => Ok((ValueType::I32, choices)),
        1 => Ok((ValueType::I64, choices)),
        _ => reference(type_count, choices),
    }
}

fn values_loop(count: Natural, type_count: &Natural, output: Sequence<ValueType>, choices: Choices)
    -> Result<(Sequence<ValueType>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((output, choices)),
        Some(previous) => {
            let (value, choices): (ValueType, Choices) = value(type_count, choices)?;
            values_loop(previous, type_count, sequence::snoc(output, value), choices)
        }
    }
}

fn values(maximum: &Natural, type_count: &Natural, choices: Choices)
    -> Result<(Sequence<ValueType>, Choices), GenerationError>
{
    let bound: Natural = natural::increment(natural::copy(maximum));
    let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
    values_loop(count, type_count, Sequence::Empty, choices)
}

fn locals_loop(count: Natural, type_count: &Natural, output: Sequence<ValueType>, choices: Choices)
    -> Result<(Sequence<ValueType>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((output, choices)),
        Some(previous) => {
            let bound: u64 = match type_count { Natural::Zero => 2, Natural::Positive(_) => 3 };
            let (selected, choices): (u64, Choices) = pick_word(bound, choices)?;
            match selected {
                0 => locals_loop(previous, type_count, sequence::snoc(output, ValueType::I32), choices),
                1 => locals_loop(previous, type_count, sequence::snoc(output, ValueType::I64), choices),
                _ => {
                    let (index, choices): (Natural, Choices) = pick_natural(type_count, choices)?;
                    locals_loop(previous, type_count,
                        sequence::snoc(output, ValueType::Ref(Nullability::Nullable, index)), choices)
                }
            }
        }
    }
}

/// Declared locals are defaultable; non-null parameters are initialized by callers.
pub fn locals(maximum: &Natural, type_count: &Natural, choices: Choices)
    -> Result<(Sequence<ValueType>, Choices), GenerationError>
{
    let bound: Natural = natural::increment(natural::copy(maximum));
    let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
    locals_loop(count, type_count, Sequence::Empty, choices)
}

fn parent(eligible: &Sequence<Natural>, choices: Choices)
    -> Result<(Option<Natural>, Choices), GenerationError>
{
    let bound: Natural = natural::increment(sequence::length(eligible));
    let (selected, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
    match natural::decrement(selected) {
        None => Ok((None, choices)),
        Some(index) => Ok((Some(natural::copy(super::lookup(eligible, index)?)), choices)),
    }
}

/// Choose the complete parent forest before signatures, including forward references.
fn headers(count: Natural, index: Natural, eligible: Sequence<Natural>, output: Sequence<Header>, choices: Choices)
    -> Result<(Sequence<Header>, Sequence<Natural>, Natural, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((output, eligible, index, choices)),
        Some(previous) => {
            let (selected, choices): (u64, Choices) = pick_word(2, choices)?;
            let finality: Finality = if selected == 0 { Finality::Final } else { Finality::NoFinal };
            let (parent, choices): (Option<Natural>, Choices) = parent(&eligible, choices)?;
            let output: Sequence<Header> = sequence::snoc(output, Header { finality, parent });
            match finality {
                Finality::Final => headers(previous, natural::increment(index), eligible, output, choices),
                Finality::NoFinal => {
                    let eligible: Sequence<Natural> = sequence::snoc(eligible, natural::copy(&index));
                    headers(previous, natural::increment(index), eligible, output, choices)
                }
            }
        }
    }
}

fn signature(parent: &Option<Natural>, config: &Config, flat: &Sequence<FuncType>,
    type_count: &Natural, choices: Choices) -> Result<(FuncType, Choices), GenerationError>
{
    match parent {
        Some(index) => Ok((copy_signature(super::lookup(flat, natural::copy(index))?), choices)),
        None => {
            let (parameters, choices): (Sequence<ValueType>, Choices) = values(&config.max_parameters, type_count, choices)?;
            let (results, choices): (Sequence<ValueType>, Choices) = values(&config.max_results, type_count, choices)?;
            Ok((FuncType { parameters, results }, choices))
        }
    }
}

fn members(pending: Sequence<Header>, config: &Config, type_count: &Natural, flat: Sequence<FuncType>,
    output: Sequence<Subtype>, choices: Choices) -> Result<(Sequence<Subtype>, Sequence<FuncType>, Choices), GenerationError>
{
    match pending {
        Sequence::Empty => Ok((output, flat, choices)),
        Sequence::Cons(cell) => {
            let (header, tail): (Header, Sequence<Header>) = *cell;
            let (signature, choices): (FuncType, Choices) = signature(&header.parent, config, &flat, type_count, choices)?;
            let flat: Sequence<FuncType> = sequence::snoc(flat, copy_signature(&signature));
            let output: Sequence<Subtype> = sequence::snoc(output,
                Subtype { finality: header.finality, parent: header.parent, signature });
            members(tail, config, type_count, flat, output, choices)
        }
    }
}

fn groups(count: Natural, config: &Config, output: Sequence<RecGroup>, flat: Sequence<FuncType>,
    eligible: Sequence<Natural>, choices: Choices) -> Result<(Sequence<RecGroup>, Sequence<FuncType>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((output, flat, choices)),
        Some(previous) => {
            let bound: Natural = natural::increment(natural::copy(&config.max_types));
            let (width, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
            let (headers, eligible, type_count, choices) = headers(width, sequence::length(&flat), eligible, Sequence::Empty, choices)?;
            let (members, flat, choices) = members(headers, config, &type_count, flat, Sequence::Empty, choices)?;
            groups(previous, config, sequence::snoc(output, RecGroup { members }), flat, eligible, choices)
        }
    }
}

pub fn generate(config: &Config, choices: Choices) -> Result<(Sequence<RecGroup>, Sequence<FuncType>, Choices), GenerationError> {
    let bound: Natural = natural::increment(natural::copy(&config.max_types));
    let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
    groups(count, config, Sequence::Empty, Sequence::Empty, Sequence::Empty, choices)
}
