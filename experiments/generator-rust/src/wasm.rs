mod ast;
mod body;
mod data;
mod memory;
mod memory_import;
mod types;
mod type_matching;
pub mod choices;
pub mod natural;
pub mod sequence;

pub use ast::{AddressType, BinaryOp, BlockType, Datas, Export, Finality, FuncType, Function, Instruction, IntegerType, Memories, Memory, MemoryImport, Module, Nullability, RecGroup, Subtype, Text, ValueType};
use ast::{copy_bytes, copy_types, join_types};
use choices::{pick_natural, pick_word, Choices, GenerationError, Source, Tape};
use natural::Natural;
use sequence::Sequence;

/// Semantic bounds are unbounded naturals; the CLI has separate resource limits.
pub struct Config {
    pub max_types: Natural,
    pub max_functions: Natural,
    pub max_parameters: Natural,
    pub max_results: Natural,
    pub max_locals: Natural,
    pub max_exports: Natural,
    pub fuel: Natural,
    pub max_memories: Natural,
    pub max_datas: Natural,
    pub max_memory_imports: Natural,
    pub work_limit: Natural,
}

pub fn sized_config(size: usize, work_limit: u64) -> Config {
    Config { max_types: natural::from_u64(size as u64),
        max_functions: natural::from_u64(size as u64),
        max_parameters: natural::from_u64(size as u64),
        max_results: natural::from_u64(size as u64),
        max_locals: natural::from_u64(size as u64),
        max_exports: natural::from_u64(size as u64), fuel: natural::from_u64(size as u64),
        max_memories: natural::from_u64(size as u64), max_datas: natural::from_u64(size as u64),
        max_memory_imports: natural::from_u64(size as u64),
        work_limit: natural::from_u64(work_limit) }
}

fn lookup<T>(values: &Sequence<T>, index: Natural) -> Result<&T, GenerationError> {
    match sequence::get(values, index) {
        Some(value) => Ok(value),
        None => Err(GenerationError::InternalInvariant),
    }
}

fn choose<T>(values: Sequence<T>, choices: Choices) -> Result<(T, Choices), GenerationError> {
    let (index, choices): (Natural, Choices) = pick_natural(&sequence::length(&values), choices)?;
    match sequence::select(values, index) {
        Some(value) => Ok((value, choices)),
        None => Err(GenerationError::InternalInvariant),
    }
}

fn subtract(left: &Natural, right: &Natural) -> Result<Natural, GenerationError> {
    match natural::difference(left, right) {
        Some(value) => Ok(value),
        None => Err(GenerationError::InternalInvariant),
    }
}

fn value_types_loop(count: Natural, values: Sequence<ValueType>, choices: Choices)
    -> Result<(Sequence<ValueType>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((values, choices)),
        Some(previous) => {
            let (selected, choices): (u64, Choices) = pick_word(2, choices)?;
            let value: ValueType = if selected == 0 { ValueType::I32 } else { ValueType::I64 };
            value_types_loop(previous, sequence::snoc(values, value), choices)
        }
    }
}

fn value_types(maximum: &Natural, choices: Choices) -> Result<(Sequence<ValueType>, Choices), GenerationError> {
    let bound: Natural = natural::increment(natural::copy(maximum));
    let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
    value_types_loop(count, Sequence::Empty, choices)
}

/// Decimal digits are least-significant first and remain in the ASCII digit range.
fn next_export_digits(digits: Sequence<u8>) -> Sequence<u8> {
    match digits {
        Sequence::Empty => sequence::cons(49, Sequence::Empty),
        Sequence::Cons(cell) => {
            let (digit, tail): (u8, Sequence<u8>) = *cell;
            if digit == 57 {
                sequence::cons(48, next_export_digits(tail))
            } else {
                sequence::cons(digit + 1, tail)
            }
        }
    }
}

fn indices_loop(count: Natural, type_count: &Natural, indices: Sequence<Natural>, choices: Choices)
    -> Result<(Sequence<Natural>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((indices, choices)),
        Some(previous) => {
            let (type_index, choices): (Natural, Choices) = pick_natural(type_count, choices)?;
            indices_loop(previous, type_count, sequence::snoc(indices, type_index), choices)
        }
    }
}

fn function_indices(maximum: &Natural, type_count: &Natural, choices: Choices)
    -> Result<(Sequence<Natural>, Choices), GenerationError>
{
    match type_count {
        Natural::Zero => Ok((Sequence::Empty, choices)),
        Natural::Positive(_) => {
            let bound: Natural = natural::increment(natural::copy(maximum));
            let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
            indices_loop(count, type_count, Sequence::Empty, choices)
        }
    }
}

fn functions_loop(pending: &Sequence<Natural>, config: &Config, types: &Sequence<FuncType>,
    indices: &Sequence<Natural>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>,
    functions: Sequence<Function>, choices: Choices)
    -> Result<(Sequence<Function>, Choices), GenerationError>
{
    match pending {
        Sequence::Empty => Ok((functions, choices)),
        Sequence::Cons(cell) => {
            let (locals, choices): (Sequence<ValueType>, Choices) = types::locals(&config.max_locals, &sequence::length(types), choices)?;
            let signature: &FuncType = lookup(types, natural::copy(&cell.0))?;
            let context: Sequence<ValueType> = join_types(&signature.parameters, &locals);
            let (body, choices): (Sequence<Instruction>, Choices) = body::generate(
                Sequence::Empty, copy_types(&signature.results), natural::copy(&config.fuel),
                &context, types, indices, groups, refs, choices)?;
            let function: Function = Function { type_index: natural::copy(&cell.0), locals, body };
            functions_loop(&cell.1, config, types, indices, groups, refs, sequence::snoc(functions, function), choices)
        }
    }
}

fn exports_loop(count: Natural, function_count: &Natural, digits: Sequence<u8>,
    exports: Sequence<Export>, choices: Choices) -> Result<(Sequence<Export>, Choices), GenerationError>
{
    match natural::decrement(count) {
        None => Ok((exports, choices)),
        Some(previous) => {
            let (function_index, choices): (Natural, Choices) = pick_natural(function_count, choices)?;
            let name: Sequence<u8> = sequence::cons(101, sequence::reverse(copy_bytes(&digits)));
            let output: Sequence<Export> = sequence::snoc(exports, Export { name, function_index });
            exports_loop(previous, function_count, next_export_digits(digits), output, choices)
        }
    }
}

fn generate_exports(maximum: &Natural, function_count: &Natural, choices: Choices)
    -> Result<(Sequence<Export>, Choices), GenerationError>
{
    match function_count {
        Natural::Zero => Ok((Sequence::Empty, choices)),
        Natural::Positive(_) => {
            let bound: Natural = natural::increment(natural::copy(maximum));
            let (count, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
            exports_loop(count, function_count, sequence::cons(48, Sequence::Empty), Sequence::Empty, choices)
        }
    }
}

fn start_indices(types: &Sequence<FuncType>, pending: &Sequence<Natural>,
    index: Natural, output: Sequence<Natural>) -> Result<Sequence<Natural>, GenerationError>
{
    match pending {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            let signature: &FuncType = lookup(types, natural::copy(&cell.0))?;
            match (&signature.parameters, &signature.results) {
                (Sequence::Empty, Sequence::Empty) => {
                    let output: Sequence<Natural> = sequence::snoc(output, natural::copy(&index));
                    start_indices(types, &cell.1, natural::increment(index), output)
                }
                _ => start_indices(types, &cell.1, natural::increment(index), output),
            }
        }
    }
}

fn generate_start(types: &Sequence<FuncType>, indices: &Sequence<Natural>, choices: Choices)
    -> Result<(Option<Natural>, Choices), GenerationError>
{
    match indices {
        Sequence::Empty => Ok((None, choices)),
        Sequence::Cons(_) => {
            let starts: Sequence<Natural> = start_indices(types, indices, Natural::Zero, Sequence::Empty)?;
            let bound: Natural = natural::increment(sequence::length(&starts));
            let (selected, choices): (Natural, Choices) = pick_natural(&bound, choices)?;
            match natural::decrement(selected) {
                None => Ok((None, choices)),
                Some(index) => Ok((Some(natural::copy(lookup(&starts, index)?)), choices)),
            }
        }
    }
}

fn declared_refs(exports: &Sequence<Export>) -> Sequence<Natural> {
    match exports {
        Sequence::Empty => Sequence::Empty,
        Sequence::Cons(cell) => sequence::cons(natural::copy(&cell.0.function_index), declared_refs(&cell.1)),
    }
}

/// Exports determine REFS before bodies; bodies and START do not declare their own references.
fn build(config: &Config, choices: Choices) -> Result<(Module, Choices), GenerationError> {
    let (types, flat, choices): (Sequence<RecGroup>, Sequence<FuncType>, Choices) = types::generate(config, choices)?;
    let (memory_imports, choices): (Sequence<MemoryImport>, Choices) =
        memory_import::generate(natural::copy(&config.max_memory_imports), choices)?;
    let (indices, choices): (Sequence<Natural>, Choices) = function_indices(&config.max_functions, &sequence::length(&flat), choices)?;
    let (exports, choices): (Sequence<Export>, Choices) = generate_exports(&config.max_exports, &sequence::length(&indices), choices)?;
    let refs: Sequence<Natural> = declared_refs(&exports);
    let (functions, choices): (Sequence<Function>, Choices) = functions_loop(&indices, config, &flat, &indices, &types, &refs, Sequence::Empty, choices)?;
    let (start, choices): (Option<Natural>, Choices) = generate_start(&flat, &indices, choices)?;
    let (memories, choices): (Memories, Choices) = memory::generate(natural::copy(&config.max_memories), choices)?;
    let (datas, choices): (Datas, Choices) = data::generate(natural::copy(&config.max_datas), choices)?;
    Ok((Module { types, functions, exports, start, memories, datas, memory_imports }, choices))
}

/// Practical sampling and replay execute exactly the same typed construction core.
pub fn sample(config: Config, seed: u64) -> Result<(Module, Choices), GenerationError> {
    let choices: Choices = Choices { source: Source::Seeded(seed), trace: Tape::Empty, remaining: natural::copy(&config.work_limit) };
    build(&config, choices)
}

/// Every supplied cell must be consumed; malformed or exhausted tapes fail explicitly.
pub fn replay(config: Config, tape: Tape) -> Result<(Module, Choices), GenerationError> {
    let choices: Choices = Choices { source: Source::Replay(tape, natural::Natural::Zero), trace: Tape::Empty, remaining: natural::copy(&config.work_limit) };
    let (module, choices): (Module, Choices) = build(&config, choices)?;
    match &choices.source {
        Source::Replay(tape, offset) => {
            match tape {
                Tape::Empty => (),
                Tape::Cons(_, _) => return Err(GenerationError::UnusedChoices(
                    natural::copy(offset), choices::length_from(tape, natural::copy(offset)))),
            }
        }
        Source::Seeded(_) => return Err(GenerationError::InternalInvariant),
    }
    Ok((module, choices))
}
