use super::ast::{copy_types, BinaryOp, BlockType, FuncType, Instruction, ValueType};
use super::choices::{pick, tick, word, Choices, GenerationError};

/// Deferred construction keeps arbitrary call arity out of recursive loop SCCs.
enum Task {
    Build(Vec<ValueType>, Vec<ValueType>, usize),
    Emit(Instruction),
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
}

#[derive(Clone, Copy)]
enum Rule {
    Finish,
    Nop,
    Drop(ValueType),
    Constant(ValueType),
    Get(usize),
    Set(usize),
    Tee(usize),
    Binary(ValueType, BinaryOp),
    Call(usize),
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
}

fn suffix(stack: &[ValueType], values: &[ValueType]) -> bool {
    if values.len() > stack.len() {
        return false;
    }
    let mut index: usize = 0;
    while index < values.len() {
        if stack[stack.len() - values.len() + index] != values[index] {
            return false;
        }
        index += 1;
    }
    true
}

fn replace_suffix(stack: &[ValueType], removed: usize, added: &[ValueType]) -> Vec<ValueType> {
    let mut output: Vec<ValueType> = Vec::new();
    let mut index: usize = 0;
    while index < stack.len() - removed {
        output.push(stack[index]);
        index += 1;
    }
    for value in added {
        output.push(*value);
    }
    output
}

fn block_signature(block: BlockType, types: &[FuncType]) -> (Vec<ValueType>, Vec<ValueType>) {
    match block {
        BlockType::Empty => (Vec::new(), Vec::new()),
        BlockType::Value(value) => {
            let mut results: Vec<ValueType> = Vec::new();
            results.push(value);
            (Vec::new(), results)
        },
        BlockType::Index(index) =>
            (copy_types(&types[index].parameters), copy_types(&types[index].results)),
    }
}

fn result_suffix(types: &[FuncType], index: usize, goal: &[ValueType]) -> bool {
    suffix(goal, &types[index].results)
}

fn rules(goal: &[ValueType], locals: &[ValueType], types: &[FuncType], functions: &[usize]) -> Vec<Rule> {
    let mut output: Vec<Rule> = Vec::new();
    output.push(Rule::Finish);
    output.push(Rule::Nop);
    output.push(Rule::Drop(ValueType::I32));
    output.push(Rule::Drop(ValueType::I64));
    let mut index: usize = 0;
    while index < locals.len() {
        output.push(Rule::Set(index));
        index += 1;
    }
    if goal.len() > 0 {
        let value: ValueType = goal[goal.len() - 1];
        output.push(Rule::Constant(value));
        output.push(Rule::Binary(value, BinaryOp::Add));
        output.push(Rule::Binary(value, BinaryOp::Sub));
        output.push(Rule::Binary(value, BinaryOp::Mul));
        let mut index: usize = 0;
        while index < locals.len() {
            if locals[index] == value {
                output.push(Rule::Get(index));
                output.push(Rule::Tee(index));
            }
            index += 1;
        }
    }
    let mut index: usize = 0;
    while index < functions.len() {
        if result_suffix(types, functions[index], goal) {
            output.push(Rule::Call(index));
        }
        index += 1;
    }
    let mut blocks: Vec<BlockType> = Vec::new();
    blocks.push(BlockType::Empty);
    if goal.len() > 0 {
        blocks.push(BlockType::Value(goal[goal.len() - 1]));
    }
    let mut index: usize = 0;
    while index < types.len() {
        if result_suffix(types, index, goal) {
            blocks.push(BlockType::Index(index));
        }
        index += 1;
    }
    for block in blocks {
        output.push(Rule::Block(block));
        output.push(Rule::Loop(block));
        output.push(Rule::If(block));
    }
    output
}

fn constant(value: ValueType, choices: Choices) -> Result<(Instruction, Choices), GenerationError> {
    match value {
        ValueType::I32 => {
            let (number, choices): (usize, Choices) = pick(1u64 << 32, choices)?;
            Ok((Instruction::Const32(number as u32), choices))
        }
        ValueType::I64 => {
            let (number, choices): (u64, Choices) = word(choices)?;
            Ok((Instruction::Const64(number), choices))
        }
    }
}

fn leaf(value: ValueType, locals: &[ValueType], choices: Choices) -> Result<(Instruction, Choices), GenerationError> {
    let mut matches: Vec<usize> = Vec::new();
    let mut index: usize = 0;
    while index < locals.len() {
        if locals[index] == value {
            matches.push(index);
        }
        index += 1;
    }
    let (selected, choices): (usize, Choices) = pick(matches.len() as u64 + 1, choices)?;
    if selected == 0 {
        constant(value, choices)
    } else {
        Ok((Instruction::LocalGet(matches[selected - 1]), choices))
    }
}

fn leaves(index: usize, goal: &[ValueType], locals: &[ValueType], body: Vec<Instruction>, choices: Choices)
    -> Result<(Vec<Instruction>, Choices), GenerationError>
{
    if index == goal.len() {
        return Ok((body, choices));
    }
    let (instruction, choices): (Instruction, Choices) = leaf(goal[index], locals, choices)?;
    let mut output: Vec<Instruction> = body;
    output.push(instruction);
    leaves(index + 1, goal, locals, output, choices)
}

/// Preserve the common stack prefix; construct the remaining requested values.
fn base(input: &[ValueType], goal: &[ValueType], locals: &[ValueType], choices: Choices)
    -> Result<(Vec<Instruction>, Choices), GenerationError>
{
    let mut common: usize = 0;
    while common < input.len() && common < goal.len() && input[common] == goal[common] {
        common += 1;
    }
    let mut body: Vec<Instruction> = Vec::new();
    let drops: u64 = (input.len() - common) as u64;
    if choices.remaining < drops {
        return Err(GenerationError::WorkLimit);
    }
    let choices: Choices = Choices { remaining: choices.remaining - drops, ..choices };
    let mut index: usize = common;
    while index < input.len() {
        body.push(Instruction::Drop);
        index += 1;
    }
    leaves(common, goal, locals, body, choices)
}

enum Stack<T> {
    Empty,
    Cons(T, Box<Stack<T>>),
}

fn push<T>(value: T, stack: Stack<T>) -> Stack<T> {
    Stack::Cons(value, Box::new(stack))
}

fn pop_body(bodies: Stack<Vec<Instruction>>) -> Result<(Vec<Instruction>, Stack<Vec<Instruction>>), GenerationError> {
    match bodies {
        Stack::Cons(body, rest) => Ok((body, *rest)),
        Stack::Empty => Err(GenerationError::InternalInvariant),
    }
}

struct Builder {
    pending: Stack<Task>,
    bodies: Stack<Vec<Instruction>>,
    choices: Choices,
}

fn step(task: Task, pending: Stack<Task>, bodies: Stack<Vec<Instruction>>, locals: &[ValueType],
    types: &[FuncType], functions: &[usize], choices: Choices) -> Result<Builder, GenerationError>
{
    let mut pending: Stack<Task> = pending;
    let mut bodies: Stack<Vec<Instruction>> = bodies;
    let mut choices: Choices = choices;
    match task {
        Task::Build(input, goal, fuel) => {
            let rule: Rule;
            if fuel == 0 {
                rule = Rule::Finish;
            } else {
                let available: Vec<Rule> = rules(&goal, locals, types, functions);
                let (selected, next): (usize, Choices) = pick(available.len() as u64, choices)?;
                choices = next;
                rule = available[selected];
            }
            if let Rule::Finish = rule {
                let (body, next): (Vec<Instruction>, Choices) = base(&input, &goal, locals, choices)?;
                choices = next;
                bodies = push(body, bodies);
            } else {
                let mut before: Vec<ValueType> = copy_types(&goal);
                match rule {
                    Rule::Finish => return Err(GenerationError::InternalInvariant),
                    Rule::Nop => pending = push(Task::Emit(Instruction::Nop), pending),
                    Rule::Drop(value) => {
                        before.push(value);
                        pending = push(Task::Emit(Instruction::Drop), pending);
                    }
                    Rule::Constant(value) => {
                        before = replace_suffix(&before, 1, &[]);
                        let (instruction, next): (Instruction, Choices) = constant(value, choices)?;
                        choices = next;
                        pending = push(Task::Emit(instruction), pending);
                    }
                    Rule::Get(index) => {
                        before = replace_suffix(&before, 1, &[]);
                        pending = push(Task::Emit(Instruction::LocalGet(index)), pending);
                    }
                    Rule::Set(index) => {
                        before.push(locals[index]);
                        pending = push(Task::Emit(Instruction::LocalSet(index)), pending);
                    }
                    Rule::Tee(index) => pending = push(Task::Emit(Instruction::LocalTee(index)), pending),
                    Rule::Binary(value, operation) => {
                        before.push(value);
                        pending = push(Task::Emit(Instruction::Binary(value, operation)), pending);
                    }
                    Rule::Call(index) => {
                        let signature: &FuncType = &types[functions[index]];
                        before = replace_suffix(&goal, signature.results.len(), &signature.parameters);
                        pending = push(Task::Emit(Instruction::Call(index)), pending);
                    }
                    Rule::Block(block) | Rule::Loop(block) | Rule::If(block) => {
                        let (parameters, results): (Vec<ValueType>, Vec<ValueType>) = block_signature(block, types);
                        before = replace_suffix(&goal, results.len(), &parameters);
                        let (prefix_fuel, next): (usize, Choices) = pick(fuel as u64, choices)?;
                        choices = next;
                        let child_fuel: usize = fuel - 1 - prefix_fuel;
                        match rule {
                            Rule::Block(_) => {
                                pending = push(Task::Block(block), pending);
                                pending = push(Task::Build(parameters, results, child_fuel), pending);
                            }
                            Rule::Loop(_) => {
                                pending = push(Task::Loop(block), pending);
                                pending = push(Task::Build(parameters, results, child_fuel), pending);
                            }
                            Rule::If(_) => {
                                before.push(ValueType::I32);
                                let (yes_fuel, next): (usize, Choices) = pick(child_fuel as u64 + 1, choices)?;
                                choices = next;
                                pending = push(Task::If(block), pending);
                                pending = push(Task::Build(copy_types(&parameters), copy_types(&results), child_fuel - yes_fuel), pending);
                                pending = push(Task::Build(parameters, results, yes_fuel), pending);
                            }
                            _ => return Err(GenerationError::InternalInvariant),
                        }
                        pending = push(Task::Build(input, before, prefix_fuel), pending);
                        return Ok(Builder { pending, bodies, choices });
                    }
                }
                pending = push(Task::Build(input, before, fuel - 1), pending);
            }
        }
        Task::Emit(instruction) => {
            let (mut body, rest): (Vec<Instruction>, Stack<Vec<Instruction>>) = pop_body(bodies)?;
            body.push(instruction);
            bodies = rest;
            bodies = push(body, bodies);
        }
        Task::Block(block) | Task::Loop(block) | Task::If(block) => {
            let (last, rest): (Vec<Instruction>, Stack<Vec<Instruction>>) = pop_body(bodies)?;
            bodies = rest;
            let instruction: Instruction = match task {
                Task::Block(_) => Instruction::Block(block, last),
                Task::Loop(_) => Instruction::Loop(block, last),
                Task::If(_) => {
                    let (yes, rest): (Vec<Instruction>, Stack<Vec<Instruction>>) = pop_body(bodies)?;
                    bodies = rest;
                    Instruction::If(block, yes, last)
                }
                _ => return Err(GenerationError::InternalInvariant),
            };
            let (mut prefix, rest): (Vec<Instruction>, Stack<Vec<Instruction>>) = pop_body(bodies)?;
            prefix.push(instruction);
            bodies = rest;
            bodies = push(prefix, bodies);
        }
    }
    Ok(Builder { pending, bodies, choices })
}

fn execute(pending: Stack<Task>, bodies: Stack<Vec<Instruction>>, locals: &[ValueType],
    types: &[FuncType], functions: &[usize], choices: Choices) -> Result<(Vec<Instruction>, Choices), GenerationError>
{
    match pending {
        Stack::Empty => {
            let (body, rest): (Vec<Instruction>, Stack<Vec<Instruction>>) = pop_body(bodies)?;
            if let Stack::Cons(_, _) = rest {
                return Err(GenerationError::InternalInvariant);
            }
            Ok((body, choices))
        }
        Stack::Cons(task, rest) => {
            let choices: Choices = tick(choices)?;
            let next: Builder = step(task, *rest, bodies, locals, types, functions, choices)?;
            execute(next.pending, next.bodies, locals, types, functions, next.choices)
        }
    }
}

/// Construct input -> output, sharing expansion fuel across all pending subgoals.
pub fn generate(input: Vec<ValueType>, output: Vec<ValueType>, fuel: usize,
    locals: &[ValueType], types: &[FuncType], functions: &[usize], choices: Choices)
    -> Result<(Vec<Instruction>, Choices), GenerationError>
{
    execute(push(Task::Build(input, output, fuel), Stack::Empty), Stack::Empty,
        locals, types, functions, choices)
}
