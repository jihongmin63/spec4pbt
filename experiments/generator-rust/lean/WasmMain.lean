import GeneratorRust
import Lean

open Lean Aeneas.Std generator_rust wasm.ast

/-- The canonical SpecTec JSON encoding stays outside the translated Rust core. -/
def wasmTag (tagName : String) (payload : Json) : Json := Json.mkObj [(tagName, payload)]

def wasmArray (values : List Json) : Json := .arr values.toArray

def wasmPositiveValue : wasm.natural.Positive → Nat
  | .One => 1
  | .Bit0 tail => 2 * wasmPositiveValue tail
  | .Bit1 tail => 2 * wasmPositiveValue tail + 1

def wasmNaturalValue : wasm.natural.Natural → Nat
  | .Zero => 0
  | .Positive value => wasmPositiveValue value

def wasmValueTypeJson (value : ValueType) : Json :=
  match value with
  | .I32 => wasmTag "NumT" (.str "I32T")
  | .I64 => wasmTag "NumT" (.str "I64T")
  | .Ref nullability index => wasmTag "RefT" (wasmTag "% %" (wasmArray [
      .str (match nullability with | .Nullable => "Null" | .NonNull => "NoNull"),
      wasmTag "VarHT" (wasmTag "StatX" (toJson (wasmNaturalValue index)))]))

def wasmBlockTypeJson (value : BlockType) : Json :=
  match value with
  | .Empty => wasmTag "ValBlockType" .null
  | .Value value => wasmTag "ValBlockType" (wasmValueTypeJson value)
  | .Index index => wasmTag "VarBlockType" (toJson (wasmNaturalValue index))

def wasmSequenceList {α : Type} : wasm.sequence.Sequence α → List α
  | .Empty => []
  | .Cons (head, tail) => head :: wasmSequenceList tail

mutual
  partial def wasmInstructionsJson (instructions : List Instruction) : Json :=
    wasmArray (instructions.map wasmInstructionJson)

  partial def wasmInstructionJson (instruction : Instruction) : Json :=
    match instruction with
    | .Const32 value => wasmTag "CONST" (wasmTag "I32" (toJson (wasmNaturalValue value)))
    | .Const64 value => wasmTag "CONST" (wasmTag "I64" (toJson (wasmNaturalValue value)))
    | .LocalGet index => wasmTag "LOCAL.GET" (toJson (wasmNaturalValue index))
    | .LocalSet index => wasmTag "LOCAL.SET" (toJson (wasmNaturalValue index))
    | .LocalTee index => wasmTag "LOCAL.TEE" (toJson (wasmNaturalValue index))
    | .RefNull index => wasmTag "REF.NULL" (wasmTag "VarHT" (wasmTag "StatX" (toJson (wasmNaturalValue index))))
    | .RefFunc index => wasmTag "REF.FUNC" (toJson (wasmNaturalValue index))
    | .Nop => .str "NOP"
    | .Drop => .str "DROP"
    | .Binary value operation => wasmTag "BINOP" (wasmTag
        (match value with | .I32 => "I32" | .I64 => "I64")
        (.str (match operation with | .Add => "IAdd" | .Sub => "ISub" | .Mul => "IMul")))
    | .Block block body => wasmTag "BLOCK" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson (wasmSequenceList body)])
    | .Loop block body => wasmTag "LOOP" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson (wasmSequenceList body)])
    | .If block yes no => wasmTag "IF % % ELSE %" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson (wasmSequenceList yes), wasmInstructionsJson (wasmSequenceList no)])
    | .Call index => wasmTag "CALL" (toJson (wasmNaturalValue index))
    | .Unreachable => .str "UNREACHABLE"
    | .Branch index => wasmTag "BR" (toJson (wasmNaturalValue index))
    | .BranchIf index => wasmTag "BR_IF" (toJson (wasmNaturalValue index))
end

def wasmSubtypeJson (subtype : Subtype) : Json :=
  wasmTag "SubT" (wasmArray [
    .str (match subtype.finality with | .Final => "Final" | .NoFinal => "NoFinal"),
    wasmArray (match subtype.parent with
      | none => []
      | some index => [wasmTag "VarHT" (wasmTag "StatX" (toJson (wasmNaturalValue index)))]),
    wasmTag "DefFuncT" (wasmTag "FuncT" (wasmArray [
      wasmArray ((wasmSequenceList subtype.signature.parameters).map wasmValueTypeJson),
      wasmArray ((wasmSequenceList subtype.signature.results).map wasmValueTypeJson)]))])

def wasmTypeJson (group : RecGroup) : Json :=
  wasmTag "RecT" (wasmArray ((wasmSequenceList group.members).map wasmSubtypeJson))

def wasmFunctionJson (function : Function) : Json :=
  Json.mkObj [
    ("FTYPE", toJson (wasmNaturalValue function.type_index)),
    ("LOCALS", wasmArray ((wasmSequenceList function.locals).map (fun value =>
      Json.mkObj [("LTYPE", wasmValueTypeJson value)]))),
    ("BODY", wasmInstructionsJson (wasmSequenceList function.body))]

def wasmExportJson (item : Export) : Json :=
  Json.mkObj [
    ("NAME", wasmArray ((wasmSequenceList item.name).map (fun byte => toJson byte.val))),
    ("EDESC", wasmTag "FuncExport" (toJson (wasmNaturalValue item.function_index)))]

def wasmMemoryTypeJson (memory : Memory) : Json :=
  wasmTag "MemoryT" (wasmArray [
    .str (match memory.address with | .I32 => "I32AT" | .I64 => "I64AT"),
    Json.mkObj [("MIN", toJson memory.minimum.val),
      ("MAX", match memory.maximum with | none => .null | some value => toJson value.val)]])

def wasmMemoriesJson : Memories → List Json
  | .Empty => []
  | .Cons memory tail =>
      Json.mkObj [("MTYPE", wasmMemoryTypeJson memory)] :: wasmMemoriesJson tail

def wasmMemoryImportJson (item : MemoryImport) : Json :=
  Json.mkObj [
    ("MODULENAME", wasmArray ((wasmSequenceList item.module_name).map (fun value => toJson (wasmNaturalValue value)))),
    ("ITEMNAME", wasmArray ((wasmSequenceList item.item_name).map (fun value => toJson (wasmNaturalValue value)))),
    ("IDESC", wasmTag "MemImport" (wasmMemoryTypeJson item.memory))]

def wasmTextChars : Text → List Char
  | .Empty => []
  | .Cons scalar tail => Char.ofNat scalar.val :: wasmTextChars tail

def wasmDatasJson : Datas → List Json
  | .Empty => []
  | .Cons payload tail =>
      Json.mkObj [("DINIT", .str (String.ofList (wasmTextChars payload))), ("DMODE", .str "Passive")]
      :: wasmDatasJson tail

def wasmModuleJson (module : wasm.ast.Module) : Json :=
  Json.mkObj [
    ("TYPES", wasmArray ((wasmSequenceList module.types).map wasmTypeJson)),
    ("GLOBALS", wasmArray []), ("TABLES", wasmArray []),
    ("MEMS", wasmArray (wasmMemoriesJson module.memories)), ("TAGS", wasmArray []),
    ("FUNCS", wasmArray ((wasmSequenceList module.functions).map wasmFunctionJson)),
    ("START", match module.start with
      | none => .null
      | some index => Json.mkObj [("SFUNC", toJson (wasmNaturalValue index))]),
    ("ELEMS", wasmArray []), ("DATAS", wasmArray (wasmDatasJson module.datas)), ("IMPORTS", wasmArray ((wasmSequenceList module.memory_imports).map wasmMemoryImportJson)),
    ("EXPORTS", wasmArray ((wasmSequenceList module.exports).map wasmExportJson))]

def wasmPositive (value : Nat) : wasm.natural.Positive :=
  if value ≤ 1 then .One else
    let tail := wasmPositive (value / 2)
    if value % 2 = 0 then .Bit0 tail else .Bit1 tail
termination_by value

def wasmNatural (value : Nat) : wasm.natural.Natural :=
  if value = 0 then .Zero else .Positive (wasmPositive value)

def wasmTapeCells : wasm.choices.Tape → List U64
  | .Empty => []
  | .Cons head tail => head :: wasmTapeCells tail

def wasmTapeFromCells (cells : List U64) : wasm.choices.Tape :=
  cells.foldr wasm.choices.Tape.Cons .Empty

def wasmReportJson (module : wasm.ast.Module) (choices : wasm.choices.Choices) : Json :=
  Json.mkObj [
    ("module", wasmModuleJson module),
    ("choices", wasmArray ((wasmTapeCells choices.trace).reverse.map (fun value => toJson value.val))),
    ("state", match choices.source with | .Seeded state => toJson state.val | .Replay _ _ => .null),
    ("remaining", toJson (wasmNaturalValue choices.remaining))]

def wasmErrorMessage (error : wasm.choices.GenerationError) : String :=
  match error with
  | .InvalidConfig => "InvalidConfig: bounds or parameter+local count exceed u32"
  | .TapeExhausted offset => s!"TapeExhausted: missing choice at offset {wasmNaturalValue offset}"
  | .ChoiceOutOfRange offset value bound =>
      s!"ChoiceOutOfRange: offset={wasmNaturalValue offset}, value={value.val}, required value < {bound.val}"
  | .UnusedChoices consumed total => s!"UnusedChoices: consumed={wasmNaturalValue consumed}, supplied={wasmNaturalValue total}"
  | .WorkLimit => "WorkLimit: generation exhausted the explicit work budget"
  | .NoReferenceProducer index => s!"NoReferenceProducer: no initialized local or declared function produces non-null type {wasmNaturalValue index}"
  | .InternalInvariant => "InternalInvariant: typed builder task/choice invariant failed"

def wasmDecimal (label value : String) : IO Nat := do
  if value.isEmpty || !value.toList.all Char.isDigit then
    throw <| IO.userError s!"{label}={value} must be an unsigned decimal integer"
  match value.toNat? with
  | some number =>
      if number >= 2^64 then throw <| IO.userError s!"{label}={value} exceeds u64"
      pure number
  | none => throw <| IO.userError s!"{label}={value} could not be parsed"

def wasmU64 (value : Nat) : IO U64 :=
  match UScalar.tryMkOpt .U64 value with
  | some value => pure value
  | none => throw <| IO.userError s!"value={value} exceeds u64"

def wasmConfig (arguments : List String) : IO wasm.Config := do
  let values ← arguments.mapM (wasmDecimal "CONFIG")
  match values with
  | [types, functions, parameters, results, locals, exports, fuel, memories, datas, imports, work] =>
      if [types, functions, parameters, results, locals, exports, memories, datas, imports].any (· > 64) || fuel > 128 || work > 1000000 then
        throw <| IO.userError "CLI resource limit: maxima <= 64, FUEL <= 128, WORK <= 1000000 required"
      return {
        max_types := wasmNatural types
        max_functions := wasmNatural functions
        max_parameters := wasmNatural parameters
        max_results := wasmNatural results
        max_locals := wasmNatural locals
        max_exports := wasmNatural exports
        fuel := wasmNatural fuel
        max_memories := wasmNatural memories
        max_datas := wasmNatural datas
        max_memory_imports := wasmNatural imports
        work_limit := wasmNatural work }
  | _ => throw <| IO.userError "Expected eleven config fields"

def wasmUnwrap (result : Result (core.result.Result (wasm.ast.Module × wasm.choices.Choices) wasm.choices.GenerationError))
    : IO (wasm.ast.Module × wasm.choices.Choices) := do
  match result.match with
  | .ok (.Ok value) => pure value
  | .ok (.Err error) => throw <| IO.userError (wasmErrorMessage error)
  | .vis (.fail error) _ => throw <| IO.userError s!"Translated Wasm generator failed: {repr error}"
  | .div => throw <| IO.userError "Translated Wasm generator diverged"

/-- Run the actual translated module builder; SIZE sets each bound without saturation. -/
def wasmSample (count size seed : Nat) : IO Unit := do
  if count == 0 || count > 1024 || size > 32 || seed + count - 1 >= 2^64 then
    throw <| IO.userError "CLI resource limit: COUNT in 1..1024, SIZE in 0..32, SEED+COUNT-1 <= u64::MAX required"
  let config ← wasmConfig (List.replicate 10 (toString size) ++ ["100000"])
  let output ← IO.getStdout
  for index in List.range count do
    let (module, _) ← wasmUnwrap (wasm.sample config (← wasmU64 (seed + index)))
    output.putStrLn (wasmModuleJson module).compress

def wasmTape (text : String) : IO wasm.choices.Tape := do
  let cells ← if text == "-" then pure [] else (text.splitOn ",").mapM (fun cell => do
    wasmU64 (← wasmDecimal "TAPE_CELL" cell))
  if cells.length > 1000000 then
    throw <| IO.userError "CLI resource limit: tape must have at most 1000000 cells"
  return wasmTapeFromCells cells

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [count, size, seed] => wasmSample (← wasmDecimal "COUNT" count) (← wasmDecimal "SIZE" size) (← wasmDecimal "SEED" seed)
  | [command, types, functions, parameters, results, locals, exports, fuel, memories, datas, imports, work, input] =>
      let config ← wasmConfig [types, functions, parameters, results, locals, exports, fuel, memories, datas, imports, work]
      let (module, choices) ← match command with
        | "sample" => wasmUnwrap (wasm.sample config (← wasmU64 (← wasmDecimal "SEED" input)))
        | "replay" => wasmUnwrap (wasm.replay config (← wasmTape input))
        | _ => throw <| IO.userError s!"Unknown command {command}; expected sample or replay"
      (← IO.getStdout).putStrLn (wasmReportJson module choices).compress
  | _ => throw <| IO.userError "Expected COUNT SIZE SEED, or sample/replay and eleven config fields plus SEED/TAPE_CSV"
