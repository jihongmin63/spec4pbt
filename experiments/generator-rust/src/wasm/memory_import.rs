use super::ast::{Memory, MemoryImport};
use super::choices::{self, pick_word, Choices, GenerationError};
use super::memory;
use super::natural::{self, Natural};
use super::sequence::{self, Sequence};

/// Original names are finite sequences of arbitrary naturals, not Unicode strings.
fn name(choices: Choices) -> Result<(Sequence<Natural>, Choices), GenerationError> {
    let (more, choices): (u64, Choices) = pick_word(2, choices)?;
    if more == 0 {
        return Ok((Sequence::Empty, choices));
    }
    let (head, choices): (Natural, Choices) = choices::natural(choices)?;
    let (tail, choices): (Sequence<Natural>, Choices) = name(choices)?;
    Ok((sequence::cons(head, tail), choices))
}

fn entry(choices: Choices) -> Result<(MemoryImport, Choices), GenerationError> {
    let (memory, choices): (Memory, Choices) = memory::memory(choices)?;
    let (module_name, choices): (Sequence<Natural>, Choices) = name(choices)?;
    let (item_name, choices): (Sequence<Natural>, Choices) = name(choices)?;
    Ok((MemoryImport { module_name, item_name, memory }, choices))
}

/// Construct descriptors and names directly, preserving import order and duplicates.
pub fn generate(maximum: Natural, choices: Choices)
    -> Result<(Sequence<MemoryImport>, Choices), GenerationError>
{
    let remaining: Natural = match natural::decrement(maximum) {
        None => return Ok((Sequence::Empty, choices)),
        Some(remaining) => remaining,
    };
    let (more, choices): (u64, Choices) = pick_word(2, choices)?;
    if more == 0 {
        return Ok((Sequence::Empty, choices));
    }
    let (head, choices): (MemoryImport, Choices) = entry(choices)?;
    let (tail, choices): (Sequence<MemoryImport>, Choices) = generate(remaining, choices)?;
    Ok((sequence::cons(head, tail), choices))
}
