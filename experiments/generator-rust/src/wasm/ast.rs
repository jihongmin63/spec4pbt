#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
    I32,
    I64,
}

pub struct FuncType {
    pub parameters: Vec<ValueType>,
    pub results: Vec<ValueType>,
}

#[derive(Clone, Copy)]
pub enum BlockType {
    Empty,
    Value(ValueType),
    Index(usize),
}

#[derive(Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
}

pub enum Instruction {
    Const32(u32),
    Const64(u64),
    LocalGet(usize),
    LocalSet(usize),
    LocalTee(usize),
    Nop,
    Drop,
    Binary(ValueType, BinaryOp),
    Block(BlockType, Vec<Instruction>),
    Loop(BlockType, Vec<Instruction>),
    If(BlockType, Vec<Instruction>, Vec<Instruction>),
    Call(usize),
}

pub struct Function {
    pub type_index: usize,
    pub locals: Vec<ValueType>,
    pub body: Vec<Instruction>,
}

pub struct Export {
    pub name: Vec<u8>,
    pub function_index: usize,
}

pub struct Module {
    pub types: Vec<FuncType>,
    pub functions: Vec<Function>,
    pub exports: Vec<Export>,
    pub start: Option<usize>,
}

pub fn copy_types(values: &[ValueType]) -> Vec<ValueType> {
    let mut output: Vec<ValueType> = Vec::new();
    for value in values {
        output.push(*value);
    }
    output
}

pub fn join_types(prefix: &[ValueType], suffix: &[ValueType]) -> Vec<ValueType> {
    let mut output: Vec<ValueType> = copy_types(prefix);
    for value in suffix {
        output.push(*value);
    }
    output
}
