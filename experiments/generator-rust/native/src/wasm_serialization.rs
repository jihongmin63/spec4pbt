use crate::wasm_choice_serialization::{natural_decimal, trace_json};
use generator_rust::wasm::{AddressType, BinaryOp, BlockType, Datas, Finality, Instruction, IntegerType, Memories, Memory, MemoryImport, Module, Nullability, RecGroup, Text, ValueType};
use generator_rust::wasm::choices::{Choices, GenerationError, Source};
use generator_rust::wasm::sequence::Sequence;

fn sequence_items<T>(values: &Sequence<T>) -> Vec<&T> {
    let mut output: Vec<&T> = Vec::new();
    let mut rest: &Sequence<T> = values;
    while let Sequence::Cons(cell) = rest {
        output.push(&cell.0);
        rest = &cell.1;
    }
    output
}

fn value_type_json(value: &ValueType) -> String {
    match value {
        ValueType::I32 => "{\"NumT\":\"I32T\"}".to_owned(),
        ValueType::I64 => "{\"NumT\":\"I64T\"}".to_owned(),
        ValueType::Ref(nullability, index) => {
            let null: &str = match nullability { Nullability::Nullable => "Null", Nullability::NonNull => "NoNull" };
            format!("{{\"RefT\":{{\"% %\":[\"{null}\",{{\"VarHT\":{{\"StatX\":{}}}}}]}}}}", natural_decimal(index))
        }
    }
}

fn value_types_json(values: &Sequence<ValueType>) -> String {
    let parts: Vec<String> = sequence_items(values).into_iter().map(value_type_json).collect();
    format!("[{}]", parts.join(","))
}

fn block_type_json(block: &BlockType) -> String {
    match block {
        BlockType::Empty => "{\"ValBlockType\":null}".to_owned(),
        BlockType::Value(value) => format!("{{\"ValBlockType\":{}}}", value_type_json(value)),
        BlockType::Index(index) => format!("{{\"VarBlockType\":{}}}", natural_decimal(index)),
    }
}

fn instruction_json(instruction: &Instruction) -> String {
    match instruction {
        Instruction::Const32(value) => format!("{{\"CONST\":{{\"I32\":{}}}}}", natural_decimal(value)),
        Instruction::Const64(value) => format!("{{\"CONST\":{{\"I64\":{}}}}}", natural_decimal(value)),
        Instruction::LocalGet(index) => format!("{{\"LOCAL.GET\":{}}}", natural_decimal(index)),
        Instruction::LocalSet(index) => format!("{{\"LOCAL.SET\":{}}}", natural_decimal(index)),
        Instruction::LocalTee(index) => format!("{{\"LOCAL.TEE\":{}}}", natural_decimal(index)),
        Instruction::RefNull(index) => format!("{{\"REF.NULL\":{{\"VarHT\":{{\"StatX\":{}}}}}}}", natural_decimal(index)),
        Instruction::RefFunc(index) => format!("{{\"REF.FUNC\":{}}}", natural_decimal(index)),
        Instruction::Nop => "\"NOP\"".to_owned(),
        Instruction::Drop => "\"DROP\"".to_owned(),
        Instruction::Binary(value, operation) => {
            let kind: &str = match value { IntegerType::I32 => "I32", IntegerType::I64 => "I64" };
            let name: &str = match operation { BinaryOp::Add => "IAdd", BinaryOp::Sub => "ISub", BinaryOp::Mul => "IMul" };
            format!("{{\"BINOP\":{{\"{kind}\":\"{name}\"}}}}")
        }
        Instruction::Block(block, body) => format!(
            "{{\"BLOCK\":[{},{}]}}", block_type_json(block), instructions_json(body)),
        Instruction::Loop(block, body) => format!(
            "{{\"LOOP\":[{},{}]}}", block_type_json(block), instructions_json(body)),
        Instruction::If(block, yes, no) => format!(
            "{{\"IF % % ELSE %\":[{},{},{}]}}",
            block_type_json(block), instructions_json(yes), instructions_json(no)),
        Instruction::Call(index) => format!("{{\"CALL\":{}}}", natural_decimal(index)),
        Instruction::Unreachable => "\"UNREACHABLE\"".to_owned(),
        Instruction::Branch(index) => format!("{{\"BR\":{}}}", natural_decimal(index)),
        Instruction::BranchIf(index) => format!("{{\"BR_IF\":{}}}", natural_decimal(index)),
    }
}

fn instructions_json(instructions: &Sequence<Instruction>) -> String {
    let parts: Vec<String> = sequence_items(instructions).into_iter().map(instruction_json).collect();
    format!("[{}]", parts.join(","))
}

fn memory_type_json(memory: &Memory) -> String {
    let address: &str = match memory.address {
        AddressType::I32 => "I32AT",
        AddressType::I64 => "I64AT",
    };
    let maximum: String = match memory.maximum {
        None => "null".to_owned(),
        Some(value) => value.to_string(),
    };
    format!("{{\"MemoryT\":[\"{address}\",{{\"MIN\":{},\"MAX\":{maximum}}}]}}", memory.minimum)
}

fn memories_json(memories: &Memories) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut rest: &Memories = memories;
    while let Memories::Cons(memory, tail) = rest {
        parts.push(format!("{{\"MTYPE\":{}}}", memory_type_json(memory)));
        rest = tail;
    }
    format!("[{}]", parts.join(","))
}

fn memory_import_json(item: &MemoryImport) -> String {
    let module_name: Vec<String> = sequence_items(&item.module_name).into_iter().map(natural_decimal).collect();
    let item_name: Vec<String> = sequence_items(&item.item_name).into_iter().map(natural_decimal).collect();
    format!("{{\"MODULENAME\":[{}],\"ITEMNAME\":[{}],\"IDESC\":{{\"MemImport\":{}}}}}",
        module_name.join(","), item_name.join(","), memory_type_json(&item.memory))
}

fn text_json(text: &Text) -> String {
    let mut output: String = "\"".to_owned();
    let mut rest: &Text = text;
    while let Text::Cons(point, tail) = rest {
        let character: char = char::from_u32(*point)
            .unwrap_or_else(|| panic!("Invalid Unicode scalar in generated data: {point}"));
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{0}'..='\u{1f}' => output.push_str(&format!("\\u{point:04x}")),
            value => output.push(value),
        }
        rest = tail;
    }
    output.push('"');
    output
}

fn datas_json(datas: &Datas) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut rest: &Datas = datas;
    while let Datas::Cons(payload, tail) = rest {
        parts.push(format!("{{\"DINIT\":{},\"DMODE\":\"Passive\"}}", text_json(payload)));
        rest = tail;
    }
    format!("[{}]", parts.join(","))
}

fn group_json(group: &RecGroup) -> String {
    let members: Vec<String> = sequence_items(&group.members).into_iter().map(|member| {
        let finality: &str = match member.finality { Finality::Final => "Final", Finality::NoFinal => "NoFinal" };
        let parent: String = match &member.parent {
            None => String::new(),
            Some(index) => format!("{{\"VarHT\":{{\"StatX\":{}}}}}", natural_decimal(index)),
        };
        format!("{{\"SubT\":[\"{finality}\",[{parent}],{{\"DefFuncT\":{{\"FuncT\":[{},{}]}}}}]}}",
            value_types_json(&member.signature.parameters), value_types_json(&member.signature.results))
    }).collect();
    format!("{{\"RecT\":[{}]}}", members.join(","))
}

pub fn module_json(module: &Module) -> String {
    let types: Vec<String> = sequence_items(&module.types).into_iter().map(group_json).collect();
    let functions: Vec<String> = sequence_items(&module.functions).into_iter().map(|function| {
        let locals: Vec<String> = sequence_items(&function.locals).into_iter().map(|value|
            format!("{{\"LTYPE\":{}}}", value_type_json(value))).collect();
        format!("{{\"FTYPE\":{},\"LOCALS\":[{}],\"BODY\":{}}}",
            natural_decimal(&function.type_index), locals.join(","), instructions_json(&function.body))
    }).collect();
    let exports: Vec<String> = sequence_items(&module.exports).into_iter().map(|export| {
        let name: Vec<String> = sequence_items(&export.name).into_iter().map(|byte| byte.to_string()).collect();
        format!("{{\"NAME\":[{}],\"EDESC\":{{\"FuncExport\":{}}}}}",
            name.join(","), natural_decimal(&export.function_index))
    }).collect();
    let imports: Vec<String> = sequence_items(&module.memory_imports).into_iter().map(memory_import_json).collect();
    let start: String = match &module.start {
        None => "null".to_owned(),
        Some(index) => format!("{{\"SFUNC\":{}}}", natural_decimal(index)),
    };
    format!(
        "{{\"TYPES\":[{}],\"GLOBALS\":[],\"TABLES\":[],\"MEMS\":{},\"TAGS\":[],\"FUNCS\":[{}],\"START\":{},\"ELEMS\":[],\"DATAS\":{},\"IMPORTS\":[{}],\"EXPORTS\":[{}]}}",
        types.join(","), memories_json(&module.memories), functions.join(","), start,
        datas_json(&module.datas), imports.join(","), exports.join(","))
}

pub fn report_json(module: &Module, choices: &Choices) -> String {
    let state: String = match &choices.source {
        Source::Seeded(state) => state.to_string(),
        Source::Replay(_, _) => "null".to_owned(),
    };
    format!("{{\"module\":{},\"choices\":{},\"state\":{},\"remaining\":{}}}",
        module_json(module), trace_json(&choices.trace), state, natural_decimal(&choices.remaining))
}

pub fn error_message(error: GenerationError) -> String {
    match error {
        GenerationError::InvalidConfig => "InvalidConfig: bounds or parameter+local count exceed u32".to_owned(),
        GenerationError::TapeExhausted(offset) => format!("TapeExhausted: missing choice at offset {}", natural_decimal(&offset)),
        GenerationError::ChoiceOutOfRange(offset, value, bound) =>
            format!("ChoiceOutOfRange: offset={}, value={value}, required value < {bound}", natural_decimal(&offset)),
        GenerationError::UnusedChoices(consumed, total) =>
            format!("UnusedChoices: consumed={}, supplied={}", natural_decimal(&consumed), natural_decimal(&total)),
        GenerationError::WorkLimit => "WorkLimit: generation exhausted the explicit work budget".to_owned(),
        GenerationError::NoReferenceProducer(index) => format!("NoReferenceProducer: no initialized local or declared function produces non-null type {}", natural_decimal(&index)),
        GenerationError::InternalInvariant => "InternalInvariant: typed builder task/choice invariant failed".to_owned(),
    }
}
