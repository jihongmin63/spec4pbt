use super::ast::{Datas, Text};
use super::choices::{pick_word, Choices, GenerationError};
use super::natural::{self, Natural};

/// Select Unicode scalars directly; the surrogate interval has no choice cells.
fn text(choices: Choices) -> Result<(Text, Choices), GenerationError> {
    let (more, choices): (u64, Choices) = pick_word(2, choices)?;
    if more == 0 {
        return Ok((Text::Empty, choices));
    }
    let (ordinal, choices): (u64, Choices) = pick_word(1112064, choices)?;
    let scalar: u32 = if ordinal < 0xd800 { ordinal as u32 } else { (ordinal + 0x800) as u32 };
    let (tail, choices): (Text, Choices) = text(choices)?;
    Ok((Text::Cons(scalar, Box::new(tail)), choices))
}

/// A passive section needs neither a memory nor an offset initializer.
pub fn generate(maximum: Natural, choices: Choices) -> Result<(Datas, Choices), GenerationError> {
    let remaining: Natural = match natural::decrement(maximum) {
        None => return Ok((Datas::Empty, choices)),
        Some(remaining) => remaining,
    };
    let (more, choices): (u64, Choices) = pick_word(2, choices)?;
    if more == 0 {
        return Ok((Datas::Empty, choices));
    }
    let (payload, choices): (Text, Choices) = text(choices)?;
    let (tail, choices): (Datas, Choices) = generate(remaining, choices)?;
    Ok((Datas::Cons(payload, Box::new(tail)), choices))
}
