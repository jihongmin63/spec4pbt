use super::ast::{copy_block_type, copy_types, copy_value, join_types, BinaryOp, BlockType, FuncType, Instruction, IntegerType, Nullability, RecGroup, ValueType};
use super::choices::{natural, pick_natural, tick, Choices, GenerationError};
use super::natural::{self as nat, Natural};
use super::type_matching::same_value;
use super::sequence::{self, Sequence};

enum Task {
    Build(Sequence<ValueType>, Sequence<ValueType>, Natural, Stack<Sequence<ValueType>>),
    Emit(Instruction),
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
}

enum Rule {
    Finish,
    Nop,
    Drop(ValueType),
    Constant(ValueType),
    Get(Natural),
    Set(Natural),
    Tee(Natural),
    Binary(IntegerType, BinaryOp),
    RefFunc(Natural),
    Call(Natural),
    Block(BlockType),
    Loop(BlockType),
    If(BlockType),
    Unreachable,
    Branch(Natural),
    BranchIf(Natural),
}

fn equal_types(left: &Sequence<ValueType>, right: &Sequence<ValueType>, groups: &Sequence<RecGroup>)
    -> Result<bool, GenerationError>
{
    match (left, right) {
        (Sequence::Empty, Sequence::Empty) => Ok(true),
        (Sequence::Cons(left), Sequence::Cons(right)) => {
            if same_value(groups, &left.0, &right.0)? {
                equal_types(&left.1, &right.1, groups)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

fn matches_after(stack: &Sequence<ValueType>, skipped: Natural, values: &Sequence<ValueType>, groups: &Sequence<RecGroup>)
    -> Result<bool, GenerationError>
{
    match nat::decrement(skipped) {
        None => equal_types(stack, values, groups),
        Some(previous) => match stack {
            Sequence::Empty => Ok(false),
            Sequence::Cons(cell) => matches_after(&cell.1, previous, values, groups),
        },
    }
}

fn suffix(stack: &Sequence<ValueType>, values: &Sequence<ValueType>, groups: &Sequence<RecGroup>)
    -> Result<bool, GenerationError>
{
    match nat::difference(&sequence::length(stack), &sequence::length(values)) {
        None => Ok(false),
        Some(skipped) => matches_after(stack, skipped, values, groups),
    }
}

fn replace_suffix(stack: &Sequence<ValueType>, removed: Natural, added: &Sequence<ValueType>)
    -> Result<Sequence<ValueType>, GenerationError>
{
    let count: Natural = super::subtract(&sequence::length(stack), &removed)?;
    match sequence::split_at(copy_types(stack), count) {
        Some((prefix, _)) => Ok(sequence::append(prefix, copy_types(added))),
        None => Err(GenerationError::InternalInvariant),
    }
}

fn block_signature(block: &BlockType, types: &Sequence<FuncType>)
    -> Result<(Sequence<ValueType>, Sequence<ValueType>), GenerationError>
{
    match block {
        BlockType::Empty => Ok((Sequence::Empty, Sequence::Empty)),
        BlockType::Value(value) => Ok((Sequence::Empty, sequence::cons(copy_value(value), Sequence::Empty))),
        BlockType::Index(index) => {
            let signature: &FuncType = super::lookup(types, nat::copy(index))?;
            Ok((copy_types(&signature.parameters), copy_types(&signature.results)))
        }
    }
}

fn set_rules(locals: &Sequence<ValueType>, index: Natural, output: Sequence<Rule>) -> Sequence<Rule> {
    match locals {
        Sequence::Empty => output,
        Sequence::Cons(cell) => {
            let output: Sequence<Rule> = sequence::snoc(output, Rule::Set(nat::copy(&index)));
            set_rules(&cell.1, nat::increment(index), output)
        }
    }
}

fn matching_locals(value: &ValueType, locals: &Sequence<ValueType>, groups: &Sequence<RecGroup>, index: Natural,
    output: Sequence<Natural>) -> Result<Sequence<Natural>, GenerationError>
{
    match locals {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            if same_value(groups, &cell.0, value)? {
                let output: Sequence<Natural> = sequence::snoc(output, nat::copy(&index));
                matching_locals(value, &cell.1, groups, nat::increment(index), output)
            } else {
                matching_locals(value, &cell.1, groups, nat::increment(index), output)
            }
        }
    }
}

fn read_rules(indices: Sequence<Natural>, output: Sequence<Rule>) -> Sequence<Rule> {
    match indices {
        Sequence::Empty => output,
        Sequence::Cons(cell) => {
            let (index, tail): (Natural, Sequence<Natural>) = *cell;
            let output: Sequence<Rule> = sequence::snoc(output, Rule::Get(nat::copy(&index)));
            let output: Sequence<Rule> = sequence::snoc(output, Rule::Tee(index));
            read_rules(tail, output)
        }
    }
}

fn call_rules(functions: &Sequence<Natural>, types: &Sequence<FuncType>, goal: &Sequence<ValueType>, groups: &Sequence<RecGroup>,
    index: Natural, output: Sequence<Rule>) -> Result<Sequence<Rule>, GenerationError>
{
    match functions {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            let signature: &FuncType = super::lookup(types, nat::copy(&cell.0))?;
            if suffix(goal, &signature.results, groups)? {
                let output: Sequence<Rule> = sequence::snoc(output, Rule::Call(nat::copy(&index)));
                call_rules(&cell.1, types, goal, groups, nat::increment(index), output)
            } else {
                call_rules(&cell.1, types, goal, groups, nat::increment(index), output)
            }
        }
    }
}

fn control_rules(block: BlockType, output: Sequence<Rule>) -> Sequence<Rule> {
    let output: Sequence<Rule> = sequence::snoc(output, Rule::Block(copy_block_type(&block)));
    let output: Sequence<Rule> = sequence::snoc(output, Rule::Loop(copy_block_type(&block)));
    sequence::snoc(output, Rule::If(block))
}

fn indexed_block_rules(types: &Sequence<FuncType>, goal: &Sequence<ValueType>, groups: &Sequence<RecGroup>,
    index: Natural, output: Sequence<Rule>) -> Result<Sequence<Rule>, GenerationError>
{
    match types {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            if suffix(goal, &cell.0.results, groups)? {
                let output: Sequence<Rule> = control_rules(BlockType::Index(nat::copy(&index)), output);
                indexed_block_rules(&cell.1, goal, groups, nat::increment(index), output)
            } else {
                indexed_block_rules(&cell.1, goal, groups, nat::increment(index), output)
            }
        }
    }
}

fn label_rules(labels: &Stack<Sequence<ValueType>>, goal: &Sequence<ValueType>, groups: &Sequence<RecGroup>,
    index: Natural, output: Sequence<Rule>) -> Result<Sequence<Rule>, GenerationError>
{
    match labels {
        Stack::Empty => Ok(output),
        Stack::Cons(values, tail) => {
            let output: Sequence<Rule> = sequence::snoc(output, Rule::Branch(nat::copy(&index)));
            if suffix(goal, values, groups)? {
                let output: Sequence<Rule> = sequence::snoc(output, Rule::BranchIf(nat::copy(&index)));
                label_rules(tail, goal, groups, nat::increment(index), output)
            } else {
                label_rules(tail, goal, groups, nat::increment(index), output)
            }
        }
    }
}

fn reference_rules(value: &ValueType, refs: &Sequence<Natural>, functions: &Sequence<Natural>,
    groups: &Sequence<RecGroup>, output: Sequence<Rule>) -> Result<Sequence<Rule>, GenerationError>
{
    match refs {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            let type_index: &Natural = super::lookup(functions, nat::copy(&cell.0))?;
            let produced: ValueType = ValueType::Ref(Nullability::NonNull, nat::copy(type_index));
            if same_value(groups, &produced, value)? {
                let output: Sequence<Rule> = sequence::snoc(output, Rule::RefFunc(nat::copy(&cell.0)));
                reference_rules(value, &cell.1, functions, groups, output)
            } else {
                reference_rules(value, &cell.1, functions, groups, output)
            }
        }
    }
}

fn numeric_rules(value: IntegerType, output: Sequence<Rule>) -> Sequence<Rule> {
    let output: Sequence<Rule> = sequence::snoc(output, Rule::Binary(value, BinaryOp::Add));
    let output: Sequence<Rule> = sequence::snoc(output, Rule::Binary(value, BinaryOp::Sub));
    sequence::snoc(output, Rule::Binary(value, BinaryOp::Mul))
}

fn result_rules(goal: &Sequence<ValueType>, locals: &Sequence<ValueType>, groups: &Sequence<RecGroup>,
    refs: &Sequence<Natural>, functions: &Sequence<Natural>, output: Sequence<Rule>) -> Result<Sequence<Rule>, GenerationError>
{
    match sequence::last(goal) {
        None => Ok(output),
        Some(value) => {
            let output: Sequence<Rule> = match value {
                ValueType::I32 => numeric_rules(IntegerType::I32, sequence::snoc(output, Rule::Constant(ValueType::I32))),
                ValueType::I64 => numeric_rules(IntegerType::I64, sequence::snoc(output, Rule::Constant(ValueType::I64))),
                ValueType::Ref(Nullability::Nullable, _) => sequence::snoc(output, Rule::Constant(copy_value(value))),
                ValueType::Ref(Nullability::NonNull, _) => output,
            };
            let indices: Sequence<Natural> = matching_locals(value, locals, groups, Natural::Zero, Sequence::Empty)?;
            reference_rules(value, refs, functions, groups, read_rules(indices, output))
        }
    }
}

fn nullable_drop_rules(types: &Sequence<FuncType>, index: Natural, output: Sequence<Rule>) -> Sequence<Rule> {
    match types {
        Sequence::Empty => output,
        Sequence::Cons(cell) => {
            let output: Sequence<Rule> = sequence::snoc(output, Rule::Drop(ValueType::Ref(Nullability::Nullable, nat::copy(&index))));
            nullable_drop_rules(&cell.1, nat::increment(index), output)
        }
    }
}

fn reference_drop_rules(refs: &Sequence<Natural>, functions: &Sequence<Natural>, output: Sequence<Rule>)
    -> Result<Sequence<Rule>, GenerationError>
{
    match refs {
        Sequence::Empty => Ok(output),
        Sequence::Cons(cell) => {
            let type_index: &Natural = super::lookup(functions, nat::copy(&cell.0))?;
            let output: Sequence<Rule> = sequence::snoc(output,
                Rule::Drop(ValueType::Ref(Nullability::NonNull, nat::copy(type_index))));
            reference_drop_rules(&cell.1, functions, output)
        }
    }
}

fn inline_block_rules(goal: &Sequence<ValueType>, output: Sequence<Rule>) -> Sequence<Rule> {
    match sequence::last(goal) {
        None => output,
        Some(value) => control_rules(BlockType::Value(copy_value(value)), output),
    }
}

fn rules(goal: &Sequence<ValueType>, locals: &Sequence<ValueType>, types: &Sequence<FuncType>,
    functions: &Sequence<Natural>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>, labels: &Stack<Sequence<ValueType>>)
    -> Result<Sequence<Rule>, GenerationError>
{
    let output: Sequence<Rule> = sequence::cons(Rule::Finish,
        sequence::cons(Rule::Nop, sequence::cons(Rule::Drop(ValueType::I32),
        sequence::cons(Rule::Drop(ValueType::I64), Sequence::Empty))));
    let output: Sequence<Rule> = set_rules(locals, Natural::Zero, output);
    let output: Sequence<Rule> = result_rules(goal, locals, groups, refs, functions, output)?;
    let output: Sequence<Rule> = call_rules(functions, types, goal, groups, Natural::Zero, output)?;
    let output: Sequence<Rule> = control_rules(BlockType::Empty, output);
    let output: Sequence<Rule> = inline_block_rules(goal, output);
    let output: Sequence<Rule> = indexed_block_rules(types, goal, groups, Natural::Zero, output)?;
    let output: Sequence<Rule> = sequence::snoc(output, Rule::Unreachable);
    let output: Sequence<Rule> = label_rules(labels, goal, groups, Natural::Zero, output)?;
    let output: Sequence<Rule> = nullable_drop_rules(types, Natural::Zero, output);
    reference_drop_rules(refs, functions, output)
}

fn constant(value: ValueType, choices: Choices) -> Result<(Instruction, Choices), GenerationError> {
    match value {
        ValueType::I32 => {
            let (number, choices): (Natural, Choices) = natural(choices)?;
            Ok((Instruction::Const32(number), choices))
        }
        ValueType::I64 => {
            let (number, choices): (Natural, Choices) = natural(choices)?;
            Ok((Instruction::Const64(number), choices))
        }
        ValueType::Ref(Nullability::Nullable, index) => Ok((Instruction::RefNull(index), choices)),
        ValueType::Ref(Nullability::NonNull, index) => Err(GenerationError::NoReferenceProducer(index)),
    }
}

fn leaf_reads(indices: Sequence<Natural>, output: Sequence<Rule>) -> Sequence<Rule> {
    match indices {
        Sequence::Empty => output,
        Sequence::Cons(cell) => {
            let (index, tail): (Natural, Sequence<Natural>) = *cell;
            leaf_reads(tail, sequence::snoc(output, Rule::Get(index)))
        }
    }
}

fn leaf(value: &ValueType, locals: &Sequence<ValueType>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>,
    functions: &Sequence<Natural>, choices: Choices) -> Result<(Instruction, Choices), GenerationError>
{
    let output: Sequence<Rule> = match value {
        ValueType::Ref(Nullability::NonNull, _) => Sequence::Empty,
        _ => sequence::cons(Rule::Constant(copy_value(value)), Sequence::Empty),
    };
    let matches: Sequence<Natural> = matching_locals(value, locals, groups, Natural::Zero, Sequence::Empty)?;
    let output: Sequence<Rule> = reference_rules(value, refs, functions, groups, leaf_reads(matches, output))?;
    if let Sequence::Empty = output {
        return match value {
            ValueType::Ref(_, index) => Err(GenerationError::NoReferenceProducer(nat::copy(index))),
            _ => Err(GenerationError::InternalInvariant),
        };
    }
    let (rule, choices): (Rule, Choices) = super::choose(output, choices)?;
    match rule {
        Rule::Constant(value) => constant(value, choices),
        Rule::Get(index) => Ok((Instruction::LocalGet(index), choices)),
        Rule::RefFunc(index) => Ok((Instruction::RefFunc(index), choices)),
        _ => Err(GenerationError::InternalInvariant),
    }
}

fn leaves(goal: &Sequence<ValueType>, locals: &Sequence<ValueType>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>,
    functions: &Sequence<Natural>, body: Sequence<Instruction>, choices: Choices)
    -> Result<(Sequence<Instruction>, Choices), GenerationError>
{
    match goal {
        Sequence::Empty => Ok((body, choices)),
        Sequence::Cons(cell) => {
            let (instruction, choices): (Instruction, Choices) = leaf(&cell.0, locals, groups, refs, functions, choices)?;
            leaves(&cell.1, locals, groups, refs, functions, sequence::snoc(body, instruction), choices)
        }
    }
}

fn drops(input: &Sequence<ValueType>, body: Sequence<Instruction>, choices: Choices)
    -> Result<(Sequence<Instruction>, Choices), GenerationError>
{
    match input {
        Sequence::Empty => Ok((body, choices)),
        Sequence::Cons(cell) => {
            let choices: Choices = tick(choices)?;
            drops(&cell.1, sequence::snoc(body, Instruction::Drop), choices)
        }
    }
}

/// Preserve the common stack prefix; construct the remaining requested values.
fn base(input: &Sequence<ValueType>, goal: &Sequence<ValueType>, locals: &Sequence<ValueType>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>,
    functions: &Sequence<Natural>, choices: Choices)
    -> Result<(Sequence<Instruction>, Choices), GenerationError>
{
    match (input, goal) {
        (Sequence::Cons(first), Sequence::Cons(second)) => {
            if same_value(groups, &first.0, &second.0)? {
                return base(&first.1, &second.1, locals, groups, refs, functions, choices);
            }
        }
        _ => (),
    }
    let (body, choices): (Sequence<Instruction>, Choices) = drops(input, Sequence::Empty, choices)?;
    leaves(goal, locals, groups, refs, functions, body, choices)
}

enum Stack<T> {
    Empty,
    Cons(T, Box<Stack<T>>),
}

fn push<T>(value: T, stack: Stack<T>) -> Stack<T> {
    Stack::Cons(value, Box::new(stack))
}

fn copy_labels(labels: &Stack<Sequence<ValueType>>) -> Stack<Sequence<ValueType>> {
    match labels {
        Stack::Empty => Stack::Empty,
        Stack::Cons(values, tail) => push(copy_types(values), copy_labels(tail)),
    }
}

fn label_types(labels: &Stack<Sequence<ValueType>>, index: Natural) -> Result<Sequence<ValueType>, GenerationError> {
    match labels {
        Stack::Empty => Err(GenerationError::InternalInvariant),
        Stack::Cons(values, tail) => match nat::decrement(index) {
            None => Ok(copy_types(values)),
            Some(previous) => label_types(tail, previous),
        },
    }
}

fn pop_body(bodies: Stack<Sequence<Instruction>>) -> Result<(Sequence<Instruction>, Stack<Sequence<Instruction>>), GenerationError> {
    match bodies {
        Stack::Cons(body, rest) => Ok((body, *rest)),
        Stack::Empty => Err(GenerationError::InternalInvariant),
    }
}

struct Builder {
    pending: Stack<Task>,
    bodies: Stack<Sequence<Instruction>>,
    choices: Choices,
}

fn step(task: Task, pending: Stack<Task>, bodies: Stack<Sequence<Instruction>>, locals: &Sequence<ValueType>,
    types: &Sequence<FuncType>, functions: &Sequence<Natural>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>, choices: Choices) -> Result<Builder, GenerationError>
{
    let mut pending: Stack<Task> = pending;
    let mut bodies: Stack<Sequence<Instruction>> = bodies;
    let mut choices: Choices = choices;
    match task {
        Task::Build(input, goal, fuel, labels) => {
            let previous: Option<Natural> = nat::decrement(nat::copy(&fuel));
            let rule: Rule = match &previous {
                None => Rule::Finish,
                Some(_) => {
                    let available: Sequence<Rule> = rules(&goal, locals, types, functions, groups, refs, &labels)?;
                    let (rule, next): (Rule, Choices) = super::choose(available, choices)?;
                    choices = next;
                    rule
                }
            };
            if let Rule::Finish = rule {
                let (body, next): (Sequence<Instruction>, Choices) = base(&input, &goal, locals, groups, refs, functions, choices)?;
                choices = next;
                bodies = push(body, bodies);
            } else {
                let previous: Natural = match previous {
                    Some(value) => value,
                    None => return Err(GenerationError::InternalInvariant),
                };
                let mut before: Sequence<ValueType> = copy_types(&goal);
                match rule {
                    Rule::Finish => return Err(GenerationError::InternalInvariant),
                    Rule::Nop => pending = push(Task::Emit(Instruction::Nop), pending),
                    Rule::Drop(value) => {
                        before = sequence::snoc(before, value);
                        pending = push(Task::Emit(Instruction::Drop), pending);
                    }
                    Rule::Constant(value) => {
                        before = replace_suffix(&before, nat::from_u64(1), &Sequence::Empty)?;
                        let (instruction, next): (Instruction, Choices) = constant(value, choices)?;
                        choices = next;
                        pending = push(Task::Emit(instruction), pending);
                    }
                    Rule::RefFunc(index) => {
                        before = replace_suffix(&before, nat::from_u64(1), &Sequence::Empty)?;
                        pending = push(Task::Emit(Instruction::RefFunc(index)), pending);
                    }
                    Rule::Get(index) => {
                        before = replace_suffix(&before, nat::from_u64(1), &Sequence::Empty)?;
                        pending = push(Task::Emit(Instruction::LocalGet(index)), pending);
                    }
                    Rule::Set(index) => {
                        before = sequence::snoc(before, copy_value(super::lookup(locals, nat::copy(&index))?));
                        pending = push(Task::Emit(Instruction::LocalSet(index)), pending);
                    }
                    Rule::Tee(index) => pending = push(Task::Emit(Instruction::LocalTee(index)), pending),
                    Rule::Binary(value, operation) => {
                        let operand: ValueType = match value { IntegerType::I32 => ValueType::I32, IntegerType::I64 => ValueType::I64 };
                        before = sequence::snoc(before, operand);
                        pending = push(Task::Emit(Instruction::Binary(value, operation)), pending);
                    }
                    Rule::Call(index) => {
                        let type_index: &Natural = super::lookup(functions, nat::copy(&index))?;
                        let signature: &FuncType = super::lookup(types, nat::copy(type_index))?;
                        before = replace_suffix(&goal, sequence::length(&signature.results), &signature.parameters)?;
                        pending = push(Task::Emit(Instruction::Call(index)), pending);
                    }
                    Rule::Unreachable => {
                        let (prefix, next): (Sequence<ValueType>, Choices) = super::value_types(&fuel, choices)?;
                        choices = next;
                        before = prefix;
                        pending = push(Task::Emit(Instruction::Unreachable), pending);
                    }
                    Rule::Branch(index) => {
                        let (prefix, next): (Sequence<ValueType>, Choices) = super::value_types(&fuel, choices)?;
                        choices = next;
                        let values: Sequence<ValueType> = label_types(&labels, nat::copy(&index))?;
                        before = join_types(&prefix, &values);
                        pending = push(Task::Emit(Instruction::Branch(index)), pending);
                    }
                    Rule::BranchIf(index) => {
                        before = sequence::snoc(before, ValueType::I32);
                        pending = push(Task::Emit(Instruction::BranchIf(index)), pending);
                    }
                    Rule::Block(ref block) | Rule::Loop(ref block) | Rule::If(ref block) => {
                        let (parameters, results): (Sequence<ValueType>, Sequence<ValueType>) = block_signature(block, types)?;
                        before = replace_suffix(&goal, sequence::length(&results), &parameters)?;
                        let (prefix_fuel, next): (Natural, Choices) = pick_natural(&fuel, choices)?;
                        choices = next;
                        let child_fuel: Natural = super::subtract(&previous, &prefix_fuel)?;
                        match rule {
                            Rule::Block(block) => {
                                let child_labels: Stack<Sequence<ValueType>> = push(copy_types(&results), copy_labels(&labels));
                                pending = push(Task::Block(block), pending);
                                pending = push(Task::Build(parameters, results, child_fuel, child_labels), pending);
                            }
                            Rule::Loop(block) => {
                                let child_labels: Stack<Sequence<ValueType>> = push(copy_types(&parameters), copy_labels(&labels));
                                pending = push(Task::Loop(block), pending);
                                pending = push(Task::Build(parameters, results, child_fuel, child_labels), pending);
                            }
                            Rule::If(block) => {
                                before = sequence::snoc(before, ValueType::I32);
                                let bound: Natural = nat::increment(nat::copy(&child_fuel));
                                let (yes_fuel, next): (Natural, Choices) = pick_natural(&bound, choices)?;
                                choices = next;
                                let no_fuel: Natural = super::subtract(&child_fuel, &yes_fuel)?;
                                let yes_labels: Stack<Sequence<ValueType>> = push(copy_types(&results), copy_labels(&labels));
                                let no_labels: Stack<Sequence<ValueType>> = copy_labels(&yes_labels);
                                pending = push(Task::If(block), pending);
                                pending = push(Task::Build(copy_types(&parameters), copy_types(&results), no_fuel, no_labels), pending);
                                pending = push(Task::Build(parameters, results, yes_fuel, yes_labels), pending);
                            }
                            _ => return Err(GenerationError::InternalInvariant),
                        }
                        pending = push(Task::Build(input, before, prefix_fuel, labels), pending);
                        return Ok(Builder { pending, bodies, choices });
                    }
                }
                pending = push(Task::Build(input, before, previous, labels), pending);
            }
        }
        Task::Emit(instruction) => {
            let (body, rest): (Sequence<Instruction>, Stack<Sequence<Instruction>>) = pop_body(bodies)?;
            bodies = push(sequence::snoc(body, instruction), rest);
        }
        Task::Block(_) | Task::Loop(_) | Task::If(_) => {
            let (last, rest): (Sequence<Instruction>, Stack<Sequence<Instruction>>) = pop_body(bodies)?;
            bodies = rest;
            let instruction: Instruction = match task {
                Task::Block(block) => Instruction::Block(block, last),
                Task::Loop(block) => Instruction::Loop(block, last),
                Task::If(block) => {
                    let (yes, rest): (Sequence<Instruction>, Stack<Sequence<Instruction>>) = pop_body(bodies)?;
                    bodies = rest;
                    Instruction::If(block, yes, last)
                }
                _ => return Err(GenerationError::InternalInvariant),
            };
            let (prefix, rest): (Sequence<Instruction>, Stack<Sequence<Instruction>>) = pop_body(bodies)?;
            bodies = push(sequence::snoc(prefix, instruction), rest);
        }
    }
    Ok(Builder { pending, bodies, choices })
}

fn execute(pending: Stack<Task>, bodies: Stack<Sequence<Instruction>>, locals: &Sequence<ValueType>,
    types: &Sequence<FuncType>, functions: &Sequence<Natural>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>, choices: Choices)
    -> Result<(Sequence<Instruction>, Choices), GenerationError>
{
    match pending {
        Stack::Empty => {
            let (body, rest): (Sequence<Instruction>, Stack<Sequence<Instruction>>) = pop_body(bodies)?;
            if let Stack::Cons(_, _) = rest {
                return Err(GenerationError::InternalInvariant);
            }
            Ok((body, choices))
        }
        Stack::Cons(task, rest) => {
            let choices: Choices = tick(choices)?;
            let next: Builder = step(task, *rest, bodies, locals, types, functions, groups, refs, choices)?;
            execute(next.pending, next.bodies, locals, types, functions, groups, refs, next.choices)
        }
    }
}

/// Construct input -> output, sharing expansion fuel across all pending subgoals.
pub fn generate(input: Sequence<ValueType>, output: Sequence<ValueType>, fuel: Natural,
    locals: &Sequence<ValueType>, types: &Sequence<FuncType>, functions: &Sequence<Natural>, groups: &Sequence<RecGroup>, refs: &Sequence<Natural>, choices: Choices)
    -> Result<(Sequence<Instruction>, Choices), GenerationError>
{
    let labels: Stack<Sequence<ValueType>> = push(copy_types(&output), Stack::Empty);
    execute(push(Task::Build(input, output, fuel, labels), Stack::Empty), Stack::Empty,
        locals, types, functions, groups, refs, choices)
}
