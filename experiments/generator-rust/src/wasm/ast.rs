use super::natural::Natural;
use super::sequence::{self, Sequence};

pub enum ValueType {
    I32,
    I64,
    Ref(Nullability, Natural),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Nullability {
    Nullable,
    NonNull,
}

#[derive(Clone, Copy)]
pub enum IntegerType {
    I32,
    I64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Finality {
    Final,
    NoFinal,
}

pub struct FuncType {
    pub parameters: Sequence<ValueType>,
    pub results: Sequence<ValueType>,
}

pub struct Subtype {
    pub finality: Finality,
    pub parent: Option<Natural>,
    pub signature: FuncType,
}

pub struct RecGroup {
    pub members: Sequence<Subtype>,
}

pub enum BlockType {
    Empty,
    Value(ValueType),
    Index(Natural),
}

#[derive(Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
}

pub enum Instruction {
    Const32(super::natural::Natural),
    Const64(Natural),
    LocalGet(Natural),
    LocalSet(Natural),
    LocalTee(Natural),
    Nop,
    Drop,
    Binary(IntegerType, BinaryOp),
    RefNull(Natural),
    RefFunc(Natural),
    Block(BlockType, Sequence<Instruction>),
    Loop(BlockType, Sequence<Instruction>),
    If(BlockType, Sequence<Instruction>, Sequence<Instruction>),
    Call(Natural),
    Unreachable,
    Branch(Natural),
    BranchIf(Natural),
}

pub struct Function {
    pub type_index: Natural,
    pub locals: Sequence<ValueType>,
    pub body: Sequence<Instruction>,
}

pub struct Export {
    pub name: Sequence<u8>,
    pub function_index: Natural,
}

#[derive(Clone, Copy)]
pub enum AddressType {
    I32,
    I64,
}

pub struct Memory {
    pub address: AddressType,
    pub minimum: u64,
    pub maximum: Option<u64>,
}

/// Import names retain the original finite lists of arbitrary natural values.
pub struct MemoryImport {
    pub module_name: Sequence<Natural>,
    pub item_name: Sequence<Natural>,
    pub memory: Memory,
}

/// The section representation has no machine-sized total length field.
pub enum Memories {
    Empty,
    Cons(Memory, Box<Memories>),
}

/// Unicode scalar values in source order, without a machine-sized string length.
pub enum Text {
    Empty,
    Cons(u32, Box<Text>),
}

pub enum Datas {
    Empty,
    Cons(Text, Box<Datas>),
}

pub struct Module {
    pub types: Sequence<RecGroup>,
    pub functions: Sequence<Function>,
    pub exports: Sequence<Export>,
    pub start: Option<Natural>,
    pub memories: Memories,
    pub datas: Datas,
    pub memory_imports: Sequence<MemoryImport>,
}

pub fn copy_types(values: &Sequence<ValueType>) -> Sequence<ValueType> {
    match values {
        Sequence::Empty => Sequence::Empty,
        Sequence::Cons(cell) => sequence::cons(copy_value(&cell.0), copy_types(&cell.1)),
    }
}

pub fn copy_value(value: &ValueType) -> ValueType {
    match value {
        ValueType::I32 => ValueType::I32,
        ValueType::I64 => ValueType::I64,
        ValueType::Ref(nullability, index) => ValueType::Ref(*nullability, super::natural::copy(index)),
    }
}

pub fn copy_signature(signature: &FuncType) -> FuncType {
    FuncType { parameters: copy_types(&signature.parameters), results: copy_types(&signature.results) }
}

pub fn join_types(prefix: &Sequence<ValueType>, suffix: &Sequence<ValueType>) -> Sequence<ValueType> {
    sequence::append(copy_types(prefix), copy_types(suffix))
}

pub fn copy_bytes(values: &Sequence<u8>) -> Sequence<u8> {
    match values {
        Sequence::Empty => Sequence::Empty,
        Sequence::Cons(cell) => sequence::cons(cell.0, copy_bytes(&cell.1)),
    }
}

pub fn copy_block_type(block: &BlockType) -> BlockType {
    match block {
        BlockType::Empty => BlockType::Empty,
        BlockType::Value(value) => BlockType::Value(copy_value(value)),
        BlockType::Index(index) => BlockType::Index(super::natural::copy(index)),
    }
}
