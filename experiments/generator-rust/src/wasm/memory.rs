use super::ast::{AddressType, Memories, Memory};
use super::choices::{pick_word, Choices, GenerationError};
use super::natural::{self, Natural};

pub(super) fn memory(choices: Choices) -> Result<(Memory, Choices), GenerationError> {
    let (width, choices): (u64, Choices) = pick_word(2, choices)?;
    let address: AddressType = if width == 0 { AddressType::I32 } else { AddressType::I64 };
    let limit: u64 = match address {
        AddressType::I32 => 65536,
        AddressType::I64 => 281474976710656,
    };
    let (minimum, choices): (u64, Choices) = pick_word(limit + 1, choices)?;
    let (has_maximum, choices): (u64, Choices) = pick_word(2, choices)?;
    if has_maximum == 0 {
        Ok((Memory { address, minimum, maximum: None }, choices))
    } else {
        let (extra, choices): (u64, Choices) = pick_word(limit - minimum + 1, choices)?;
        Ok((Memory { address, minimum,
            maximum: Some(minimum + extra) }, choices))
    }
}

/// Construct each memory directly, with no machine-sized section-count choice.
pub fn generate(maximum: Natural, choices: Choices) -> Result<(Memories, Choices), GenerationError> {
    let remaining: Natural = match natural::decrement(maximum) {
        None => return Ok((Memories::Empty, choices)),
        Some(remaining) => remaining,
    };
    let (more, choices): (u64, Choices) = pick_word(2, choices)?;
    if more == 0 {
        return Ok((Memories::Empty, choices));
    }
    let (head, choices): (Memory, Choices) = memory(choices)?;
    let (tail, choices): (Memories, Choices) = generate(remaining, choices)?;
    Ok((Memories::Cons(head, Box::new(tail)), choices))
}
