use crate::generator::next_random;
use super::natural::{self, Natural, Positive};

pub enum Tape {
    Empty,
    Cons(u64, Box<Tape>),
}

pub enum GenerationError {
    InvalidConfig,
    TapeExhausted(Natural),
    ChoiceOutOfRange(Natural, u64, u64),
    UnusedChoices(Natural, Natural),
    WorkLimit,
    InternalInvariant,
    NoReferenceProducer(Natural),
}

pub enum Source {
    Seeded(u64),
    Replay(Tape, Natural),
}

pub struct Choices {
    pub source: Source,
    /// Most recent choice first; frontends restore chronological order.
    pub trace: Tape,
    pub remaining: Natural,
}

pub fn length_from(tape: &Tape, offset: Natural) -> Natural {
    match tape {
        Tape::Empty => offset,
        Tape::Cons(_, tail) => length_from(tail, natural::increment(offset)),
    }
}

pub fn tick(choices: Choices) -> Result<Choices, GenerationError> {
    match natural::decrement(choices.remaining) {
        None => Err(GenerationError::WorkLimit),
        Some(remaining) => Ok(Choices { remaining, ..choices }),
    }
}

/// Consume a full word. Exhausted replay never switches to a PRNG.
pub fn word(choices: Choices) -> Result<(u64, Choices), GenerationError> {
    let choices: Choices = tick(choices)?;
    let (value, source): (u64, Source) = match choices.source {
        Source::Seeded(state) => {
            let (value, state): (u64, u64) = next_random(state);
            (value, Source::Seeded(state))
        }
        Source::Replay(tape, offset) => match tape {
            Tape::Empty => return Err(GenerationError::TapeExhausted(offset)),
            Tape::Cons(value, tail) =>
                (value, Source::Replay(*tail, natural::increment(offset))),
        },
    };
    let trace: Tape = Tape::Cons(value, Box::new(choices.trace));
    Ok((value, Choices { source, trace, remaining: choices.remaining }))
}

/// Replay cells are actual bounded choices; seeded draws record their residue.
pub fn pick_word(bound: u64, choices: Choices) -> Result<(u64, Choices), GenerationError> {
    if bound == 0 {
        return Err(GenerationError::InternalInvariant);
    }
    let choices: Choices = tick(choices)?;
    let (value, source): (u64, Source) = match choices.source {
        Source::Seeded(state) => {
            let (value, state): (u64, u64) = next_random(state);
            (value % bound, Source::Seeded(state))
        }
        Source::Replay(tape, offset) => match tape {
            Tape::Empty => return Err(GenerationError::TapeExhausted(offset)),
            Tape::Cons(value, tail) => {
                if value >= bound {
                    return Err(GenerationError::ChoiceOutOfRange(offset, value, bound));
                }
                (value, Source::Replay(*tail, natural::increment(offset)))
            }
        },
    };
    let trace: Tape = Tape::Cons(value, Box::new(choices.trace));
    Ok((value, Choices { source, trace, remaining: choices.remaining }))
}

/// Only vector indices use usize; a narrowing cast must never truncate a choice.
pub fn pick(bound: u64, choices: Choices) -> Result<(usize, Choices), GenerationError> {
    let (value, choices): (u64, Choices) = pick_word(bound, choices)?;
    if value > usize::MAX as u64 {
        return Err(GenerationError::InternalInvariant);
    }
    Ok((value as usize, choices))
}

/// Select below any positive natural bound, preserving compact word-range tapes.
pub fn pick_natural(bound: &Natural, choices: Choices) -> Result<(Natural, Choices), GenerationError> {
    match natural::to_u64(bound) {
        Some(word_bound) => {
            let (value, choices): (u64, Choices) = pick_word(word_bound, choices)?;
            Ok((natural::from_u64(value), choices))
        }
        None => {
            let (tag, choices): (u64, Choices) = pick_word(2, choices)?;
            if tag == 0 {
                Ok((Natural::Zero, choices))
            } else {
                let previous: Natural = match natural::decrement(natural::copy(bound)) {
                    Some(value) => value,
                    None => return Err(GenerationError::InternalInvariant),
                };
                let (value, choices): (Natural, Choices) = pick_natural(&previous, choices)?;
                Ok((natural::increment(value), choices))
            }
        }
    }
}

/// A finite sequence selects every positive binary numeral without a bit-count bound.
pub fn positive(choices: Choices) -> Result<(Positive, Choices), GenerationError> {
    let (tag, choices): (u64, Choices) = pick_word(3, choices)?;
    if tag == 0 {
        Ok((Positive::One, choices))
    } else {
        let (tail, choices): (Positive, Choices) = positive(choices)?;
        let value: Positive = if tag == 1 {
            Positive::Bit0(Box::new(tail))
        } else {
            Positive::Bit1(Box::new(tail))
        };
        Ok((value, choices))
    }
}

/// Preserve compact literal tapes; the extra choice opens the unbounded binary domain.
pub fn natural(choices: Choices) -> Result<(Natural, Choices), GenerationError> {
    let (value, choices): (u64, Choices) = pick_word((1u64 << 32) + 1, choices)?;
    if value < (1u64 << 32) {
        Ok((natural::from_u64(value), choices))
    } else {
        let (value, choices): (Positive, Choices) = positive(choices)?;
        Ok((Natural::Positive(value), choices))
    }
}
