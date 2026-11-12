use generator_rust::wasm::{BinaryOp, BlockType, Instruction, Module, ValueType};
use generator_rust::wasm::choices::{Choices, GenerationError, Source};

fn value_type_json(value: ValueType) -> &'static str {
    match value {
        ValueType::I32 => "{\"NumT\":\"I32T\"}",
        ValueType::I64 => "{\"NumT\":\"I64T\"}",
    }
}

fn value_types_json(values: &[ValueType]) -> String {
    let parts: Vec<&str> = values.iter().map(|value| value_type_json(*value)).collect();
    format!("[{}]", parts.join(","))
}

fn block_type_json(block: BlockType) -> String {
    match block {
        BlockType::Empty => "{\"ValBlockType\":null}".to_owned(),
        BlockType::Value(value) => format!("{{\"ValBlockType\":{}}}", value_type_json(value)),
        BlockType::Index(index) => format!("{{\"VarBlockType\":{index}}}"),
    }
}

fn instruction_json(instruction: &Instruction) -> String {
    match instruction {
        Instruction::Const32(value) => format!("{{\"CONST\":{{\"I32\":{value}}}}}"),
        Instruction::Const64(value) => format!("{{\"CONST\":{{\"I64\":{value}}}}}"),
        Instruction::LocalGet(index) => format!("{{\"LOCAL.GET\":{index}}}"),
        Instruction::LocalSet(index) => format!("{{\"LOCAL.SET\":{index}}}"),
        Instruction::LocalTee(index) => format!("{{\"LOCAL.TEE\":{index}}}"),
        Instruction::Nop => "\"NOP\"".to_owned(),
        Instruction::Drop => "\"DROP\"".to_owned(),
        Instruction::Binary(value, operation) => {
            let kind: &str = match value { ValueType::I32 => "I32", ValueType::I64 => "I64" };
            let name: &str = match operation { BinaryOp::Add => "IAdd", BinaryOp::Sub => "ISub", BinaryOp::Mul => "IMul" };
            format!("{{\"BINOP\":{{\"{kind}\":\"{name}\"}}}}")
        }
        Instruction::Block(block, body) => format!(
            "{{\"BLOCK\":[{},{}]}}", block_type_json(*block), instructions_json(body)),
        Instruction::Loop(block, body) => format!(
            "{{\"LOOP\":[{},{}]}}", block_type_json(*block), instructions_json(body)),
        Instruction::If(block, yes, no) => format!(
            "{{\"IF % % ELSE %\":[{},{},{}]}}",
            block_type_json(*block), instructions_json(yes), instructions_json(no)),
        Instruction::Call(index) => format!("{{\"CALL\":{index}}}"),
    }
}

fn instructions_json(instructions: &[Instruction]) -> String {
    let parts: Vec<String> = instructions.iter().map(instruction_json).collect();
    format!("[{}]", parts.join(","))
}

pub fn module_json(module: &Module) -> String {
    let types: Vec<String> = module.types.iter().map(|signature| format!(
        "{{\"RecT\":[{{\"SubT\":[\"Final\",[],{{\"DefFuncT\":{{\"FuncT\":[{},{}]}}}}]}}]}}",
        value_types_json(&signature.parameters), value_types_json(&signature.results))).collect();
    let functions: Vec<String> = module.functions.iter().map(|function| {
        let locals: Vec<String> = function.locals.iter().map(|value|
            format!("{{\"LTYPE\":{}}}", value_type_json(*value))).collect();
        format!("{{\"FTYPE\":{},\"LOCALS\":[{}],\"BODY\":{}}}",
            function.type_index, locals.join(","), instructions_json(&function.body))
    }).collect();
    let exports: Vec<String> = module.exports.iter().map(|export| {
        let name: Vec<String> = export.name.iter().map(|byte| byte.to_string()).collect();
        format!("{{\"NAME\":[{}],\"EDESC\":{{\"FuncExport\":{}}}}}",
            name.join(","), export.function_index)
    }).collect();
    let start: String = match module.start {
        None => "null".to_owned(),
        Some(index) => format!("{{\"SFUNC\":{index}}}"),
    };
    format!(
        "{{\"TYPES\":[{}],\"GLOBALS\":[],\"TABLES\":[],\"MEMS\":[],\"TAGS\":[],\"FUNCS\":[{}],\"START\":{},\"ELEMS\":[],\"DATAS\":[],\"IMPORTS\":[],\"EXPORTS\":[{}]}}",
        types.join(","), functions.join(","), start, exports.join(","))
}

pub fn report_json(module: &Module, choices: &Choices) -> String {
    let trace: Vec<String> = choices.trace.iter().map(|value| value.to_string()).collect();
    let state: String = match &choices.source {
        Source::Seeded(state) => state.to_string(),
        Source::Replay(_, _) => "null".to_owned(),
    };
    format!("{{\"module\":{},\"choices\":[{}],\"state\":{},\"remaining\":{}}}",
        module_json(module), trace.join(","), state, choices.remaining)
}

pub fn error_message(error: GenerationError) -> String {
    match error {
        GenerationError::InvalidConfig => "InvalidConfig: bounds or parameter+local count exceed u32".to_owned(),
        GenerationError::TapeExhausted(offset) => format!("TapeExhausted: missing choice at offset {offset}"),
        GenerationError::ChoiceOutOfRange(offset, value, bound) =>
            format!("ChoiceOutOfRange: offset={offset}, value={value}, required value < {bound}"),
        GenerationError::UnusedChoices(consumed, total) =>
            format!("UnusedChoices: consumed={consumed}, supplied={total}"),
        GenerationError::WorkLimit => "WorkLimit: generation exhausted the explicit work budget".to_owned(),
        GenerationError::InternalInvariant => "InternalInvariant: typed builder task/choice invariant failed".to_owned(),
    }
}
