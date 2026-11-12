mod ast;
mod body;
pub mod choices;

pub use ast::{BinaryOp, BlockType, Export, FuncType, Function, Instruction, Module, ValueType};
use ast::{copy_types, join_types};
use choices::{pick, Choices, GenerationError, Source};

/// Semantic bounds are explicit; the CLI applies separate, rejecting resource limits.
pub struct Config {
    pub max_types: usize,
    pub max_functions: usize,
    pub max_parameters: usize,
    pub max_results: usize,
    pub max_locals: usize,
    pub max_exports: usize,
    pub fuel: usize,
    pub work_limit: u64,
}

pub fn sized_config(size: usize, work_limit: u64) -> Config {
    Config { max_types: size, max_functions: size, max_parameters: size,
        max_results: size, max_locals: size, max_exports: size, fuel: size, work_limit }
}

fn validate(config: &Config) -> Result<(), GenerationError> {
    if config.max_types as u64 > u32::MAX as u64
        || config.max_functions as u64 > u32::MAX as u64
        || config.max_parameters as u64 > u32::MAX as u64
        || config.max_results as u64 > u32::MAX as u64
        || config.max_locals as u64 > u32::MAX as u64
        || config.max_exports as u64 > u32::MAX as u64
        || config.fuel as u64 > u32::MAX as u64
    {
        return Err(GenerationError::InvalidConfig);
    }
    if config.max_parameters as u64 + config.max_locals as u64 > u32::MAX as u64 {
        return Err(GenerationError::InvalidConfig);
    }
    Ok(())
}

fn value_types_loop(count: usize, values: Vec<ValueType>, choices: Choices) -> Result<(Vec<ValueType>, Choices), GenerationError> {
    if count == 0 {
        return Ok((values, choices));
    }
    let (selected, choices): (usize, Choices) = pick(2, choices)?;
    let mut output: Vec<ValueType> = values;
    output.push(if selected == 0 { ValueType::I32 } else { ValueType::I64 });
    value_types_loop(count - 1, output, choices)
}

fn value_types(maximum: usize, choices: Choices) -> Result<(Vec<ValueType>, Choices), GenerationError> {
    let (count, choices): (usize, Choices) = pick(maximum as u64 + 1, choices)?;
    value_types_loop(count, Vec::new(), choices)
}

fn export_name(index: usize) -> Vec<u8> {
    let mut reversed: Vec<u8> = Vec::new();
    let mut value: usize = index;
    loop {
        reversed.push(48 + (value % 10) as u8);
        value /= 10;
        if value == 0 {
            break;
        }
    }
    let mut name: Vec<u8> = Vec::new();
    name.push(101);
    let mut offset: usize = reversed.len();
    while offset > 0 {
        offset -= 1;
        name.push(reversed[offset]);
    }
    name
}

fn types_loop(count: usize, config: &Config, types: Vec<FuncType>, choices: Choices) -> Result<(Vec<FuncType>, Choices), GenerationError> {
    if count == 0 {
        return Ok((types, choices));
    }
    let (parameters, choices): (Vec<ValueType>, Choices) = value_types(config.max_parameters, choices)?;
    let (results, choices): (Vec<ValueType>, Choices) = value_types(config.max_results, choices)?;
    let mut output: Vec<FuncType> = types;
    output.push(FuncType { parameters, results });
    types_loop(count - 1, config, output, choices)
}

fn generate_types(config: &Config, choices: Choices) -> Result<(Vec<FuncType>, Choices), GenerationError> {
    let (count, choices): (usize, Choices) = pick(config.max_types as u64 + 1, choices)?;
    types_loop(count, config, Vec::new(), choices)
}

fn indices_loop(count: usize, type_count: usize, indices: Vec<usize>, choices: Choices) -> Result<(Vec<usize>, Choices), GenerationError> {
    if count == 0 {
        return Ok((indices, choices));
    }
    let (type_index, choices): (usize, Choices) = pick(type_count as u64, choices)?;
    let mut output: Vec<usize> = indices;
    output.push(type_index);
    indices_loop(count - 1, type_count, output, choices)
}

fn function_indices(maximum: usize, type_count: usize, choices: Choices) -> Result<(Vec<usize>, Choices), GenerationError> {
    if type_count == 0 {
        return Ok((Vec::new(), choices));
    }
    let (count, choices): (usize, Choices) = pick(maximum as u64 + 1, choices)?;
    indices_loop(count, type_count, Vec::new(), choices)
}

fn functions_loop(index: usize, config: &Config, types: &[FuncType], indices: &[usize], functions: Vec<Function>, choices: Choices)
    -> Result<(Vec<Function>, Choices), GenerationError>
{
    if index == indices.len() {
        return Ok((functions, choices));
    }
    let (locals, choices): (Vec<ValueType>, Choices) = value_types(config.max_locals, choices)?;
    let signature: &FuncType = &types[indices[index]];
    let context: Vec<ValueType> = join_types(&signature.parameters, &locals);
    let (body, choices): (Vec<Instruction>, Choices) = body::generate(
        Vec::new(), copy_types(&signature.results), config.fuel, &context, types, indices, choices)?;
    let mut output: Vec<Function> = functions;
    output.push(Function { type_index: indices[index], locals, body });
    functions_loop(index + 1, config, types, indices, output, choices)
}

fn exports_loop(count: usize, function_count: usize, exports: Vec<Export>, choices: Choices) -> Result<(Vec<Export>, Choices), GenerationError> {
    if count == 0 {
        return Ok((exports, choices));
    }
    let (function_index, choices): (usize, Choices) = pick(function_count as u64, choices)?;
    let mut output: Vec<Export> = exports;
    output.push(Export { name: export_name(output.len()), function_index });
    exports_loop(count - 1, function_count, output, choices)
}

fn generate_exports(maximum: usize, function_count: usize, choices: Choices) -> Result<(Vec<Export>, Choices), GenerationError> {
    if function_count == 0 {
        return Ok((Vec::new(), choices));
    }
    let (count, choices): (usize, Choices) = pick(maximum as u64 + 1, choices)?;
    exports_loop(count, function_count, Vec::new(), choices)
}

fn is_start(types: &[FuncType], index: usize) -> bool {
    types[index].parameters.len() == 0 && types[index].results.len() == 0
}

fn generate_start(types: &[FuncType], indices: &[usize], choices: Choices) -> Result<(Option<usize>, Choices), GenerationError> {
    if indices.len() == 0 {
        return Ok((None, choices));
    }
    let mut starts: Vec<usize> = Vec::new();
    let mut index: usize = 0;
    while index < indices.len() {
        if is_start(types, indices[index]) {
            starts.push(index);
        }
        index += 1;
    }
    let (selected, choices): (usize, Choices) = pick(starts.len() as u64 + 1, choices)?;
    if selected == 0 {
        Ok((None, choices))
    } else {
        Ok((Some(starts[selected - 1]), choices))
    }
}

/// Choose module declarations before bodies, so calls can use any declared function.
fn build(config: &Config, choices: Choices) -> Result<(Module, Choices), GenerationError> {
    validate(config)?;
    let (types, choices): (Vec<FuncType>, Choices) = generate_types(config, choices)?;
    let (indices, choices): (Vec<usize>, Choices) = function_indices(config.max_functions, types.len(), choices)?;
    let (functions, choices): (Vec<Function>, Choices) = functions_loop(0, config, &types, &indices, Vec::new(), choices)?;
    let (exports, choices): (Vec<Export>, Choices) = generate_exports(config.max_exports, indices.len(), choices)?;
    let (start, choices): (Option<usize>, Choices) = generate_start(&types, &indices, choices)?;
    Ok((Module { types, functions, exports, start }, choices))
}

/// Practical sampling and replay execute exactly the same typed construction core.
pub fn sample(config: Config, seed: u64) -> Result<(Module, Choices), GenerationError> {
    let choices: Choices = Choices { source: Source::Seeded(seed), trace: Vec::new(), remaining: config.work_limit };
    build(&config, choices)
}

/// Every supplied cell must be consumed; malformed or exhausted tapes fail explicitly.
pub fn replay(config: Config, tape: Vec<u64>) -> Result<(Module, Choices), GenerationError> {
    let choices: Choices = Choices { source: Source::Replay(tape, 0), trace: Vec::new(), remaining: config.work_limit };
    let (module, choices): (Module, Choices) = build(&config, choices)?;
    match &choices.source {
        Source::Replay(tape, offset) => {
            if *offset != tape.len() {
                return Err(GenerationError::UnusedChoices(*offset, tape.len()));
            }
        }
        Source::Seeded(_) => return Err(GenerationError::InternalInvariant),
    }
    Ok((module, choices))
}
