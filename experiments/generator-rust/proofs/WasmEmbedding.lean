import GeneratorRust
import WasmSequence
import WasmDataEncoding
import WasmSpecification

set_option autoImplicit false

namespace RustWasm
open Aeneas.Std generator_rust wasm.ast

/-- The original pinned specification AST, without JSON or normalization. -/
def valueType : ValueType → SpecTec.valtype
  | .I32 => .NumT .I32T
  | .I64 => .NumT .I64T
  | .Ref nullability index => .RefT (.«% %»
      (match nullability with | .Nullable => .Null | .NonNull => .NoNull)
      (.VarHT (.StatX (naturalValue index))))

def blockType : BlockType → SpecTec.blocktype
  | .Empty => .ValBlockType none
  | .Value value => .ValBlockType (some (valueType value))
  | .Index index => .VarBlockType (naturalValue index)

def binaryOp : BinaryOp → SpecTec.ibinop
  | .Add => .IAdd
  | .Sub => .ISub
  | .Mul => .IMul

mutual
def instruction : Instruction → SpecTec.instr
  | .Const32 value => .CONST (.I32 (naturalValue value))
  | .Const64 value => .CONST (.I64 (naturalValue value))
  | .LocalGet index => .«LOCAL.GET» (naturalValue index)
  | .LocalSet index => .«LOCAL.SET» (naturalValue index)
  | .LocalTee index => .«LOCAL.TEE» (naturalValue index)
  | .RefNull index => .«REF.NULL» (.VarHT (.StatX (naturalValue index)))
  | .RefFunc index => .«REF.FUNC» (naturalValue index)
  | .Nop => .NOP
  | .Drop => .DROP
  | .Binary .I32 operation => .BINOP (.I32 (binaryOp operation))
  | .Binary .I64 operation => .BINOP (.I64 (binaryOp operation))
  | .Block block body => .BLOCK (blockType block) (instructionSequence body)
  | .Loop block body => .LOOP (blockType block) (instructionSequence body)
  | .If block yes no => .«IF % % ELSE %» (blockType block)
      (instructionSequence yes) (instructionSequence no)
  | .Call index => .CALL (naturalValue index)
  | .Unreachable => .UNREACHABLE
  | .Branch index => .BR (naturalValue index)
  | .BranchIf index => .BR_IF (naturalValue index)
termination_by item => sizeOf item

def instructionSequence : wasm.sequence.Sequence Instruction → List SpecTec.instr
  | .Empty => []
  | .Cons (head, tail) => instruction head :: instructionSequence tail
termination_by items => sizeOf items
end

def functionType (signature : FuncType) : SpecTec.rectype :=
  .RecT [.SubT .Final [] (.DefFuncT (.FuncT
    ((sequenceValues signature.parameters).map valueType) ((sequenceValues signature.results).map valueType)))]

def subtype (item : Subtype) : SpecTec.subtype :=
  .SubT (match item.finality with | .Final => .Final | .NoFinal => .NoFinal)
    (match item.parent with | none => [] | some index => [.VarHT (.StatX (naturalValue index))])
    (.DefFuncT (.FuncT ((sequenceValues item.signature.parameters).map valueType)
      ((sequenceValues item.signature.results).map valueType)))

def recursiveGroup (item : RecGroup) : SpecTec.rectype :=
  .RecT ((sequenceValues item.members).map subtype)

def function (item : Function) : SpecTec.func :=
  ⟨naturalValue item.type_index, (sequenceValues item.locals).map (fun value => ⟨valueType value⟩),
    instructionSequence item.body⟩

def exportEntry (item : Export) : SpecTec.export :=
  ⟨(sequenceValues item.name).map (fun byte => byte.val), .FuncExport (naturalValue item.function_index)⟩

def memory (item : Memory) : SpecTec.memory :=
  ⟨.MemoryT (match item.address with | .I32 => .I32AT | .I64 => .I64AT)
    ⟨item.minimum.val, item.maximum.map (fun value => value.val)⟩⟩

def memoryImport (item : MemoryImport) : SpecTec.«import» :=
  ⟨(sequenceValues item.module_name).map naturalValue,
    (sequenceValues item.item_name).map naturalValue, .MemImport (memory item.memory).MTYPE⟩

def memories : Memories → List SpecTec.memory
  | .Empty => []
  | .Cons head tail => memory head :: memories tail

def datas : Datas → List SpecTec.data
  | .Empty => []
  | .Cons payload tail => ⟨textValue payload, .Passive⟩ :: datas tail

/-- All represented sections are converted structurally; omitted sections stay empty. -/
def embed (item : wasm.ast.Module) : SpecTec.module where
  TYPES := (sequenceValues item.types).map recursiveGroup
  GLOBALS := []
  TABLES := []
  MEMS := memories item.memories
  TAGS := []
  FUNCS := (sequenceValues item.functions).map function
  START := item.start.map (fun index => ⟨(naturalValue index)⟩)
  ELEMS := []
  DATAS := datas item.datas
  IMPORTS := (sequenceValues item.memory_imports).map memoryImport
  EXPORTS := (sequenceValues item.exports).map exportEntry

@[simp] theorem embed_memories (item : wasm.ast.Module) :
    (embed item).MEMS = memories item.memories := rfl

end RustWasm
