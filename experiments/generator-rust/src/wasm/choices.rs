use crate::generator::next_random;

pub enum GenerationError {
    InvalidConfig,
    TapeExhausted(usize),
    ChoiceOutOfRange(usize, u64, u64),
    UnusedChoices(usize, usize),
    WorkLimit,
    InternalInvariant,
}

pub enum Source {
    Seeded(u64),
    Replay(Vec<u64>, usize),
}

pub struct Choices {
    pub source: Source,
    pub trace: Vec<u64>,
    pub remaining: u64,
}

pub fn tick(choices: Choices) -> Result<Choices, GenerationError> {
    if choices.remaining == 0 {
        return Err(GenerationError::WorkLimit);
    }
    Ok(Choices { remaining: choices.remaining - 1, ..choices })
}

/// Consume a full word. Exhausted replay never switches to a PRNG.
pub fn word(choices: Choices) -> Result<(u64, Choices), GenerationError> {
    let choices: Choices = tick(choices)?;
    let (value, source): (u64, Source) = match choices.source {
        Source::Seeded(state) => {
            let (value, state): (u64, u64) = next_random(state);
            (value, Source::Seeded(state))
        }
        Source::Replay(tape, offset) => {
            if offset == tape.len() {
                return Err(GenerationError::TapeExhausted(offset));
            }
            let value: u64 = tape[offset];
            (value, Source::Replay(tape, offset + 1))
        }
    };
    let mut trace: Vec<u64> = choices.trace;
    trace.push(value);
    Ok((value, Choices { source, trace, remaining: choices.remaining }))
}

/// Replay cells are actual bounded choices; seeded draws record their residue.
pub fn pick(bound: u64, choices: Choices) -> Result<(usize, Choices), GenerationError> {
    if bound == 0 {
        return Err(GenerationError::InternalInvariant);
    }
    let choices: Choices = tick(choices)?;
    let (value, source): (u64, Source) = match choices.source {
        Source::Seeded(state) => {
            let (value, state): (u64, u64) = next_random(state);
            (value % bound, Source::Seeded(state))
        }
        Source::Replay(tape, offset) => {
            if offset == tape.len() {
                return Err(GenerationError::TapeExhausted(offset));
            }
            let value: u64 = tape[offset];
            if value >= bound {
                return Err(GenerationError::ChoiceOutOfRange(offset, value, bound));
            }
            (value, Source::Replay(tape, offset + 1))
        }
    };
    let mut trace: Vec<u64> = choices.trace;
    trace.push(value);
    Ok((value as usize, Choices { source, trace, remaining: choices.remaining }))
}
