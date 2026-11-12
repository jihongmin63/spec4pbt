import GeneratorRust
import Lean

open Lean Aeneas.Std generator_rust wasm.ast

/-- The canonical SpecTec JSON encoding stays outside the translated Rust core. -/
def wasmTag (tagName : String) (payload : Json) : Json := Json.mkObj [(tagName, payload)]

def wasmArray (values : List Json) : Json := .arr values.toArray

def wasmValueTypeJson (value : ValueType) : Json :=
  wasmTag "NumT" (.str (match value with | .I32 => "I32T" | .I64 => "I64T"))

def wasmBlockTypeJson (value : BlockType) : Json :=
  match value with
  | .Empty => wasmTag "ValBlockType" .null
  | .Value value => wasmTag "ValBlockType" (wasmValueTypeJson value)
  | .Index index => wasmTag "VarBlockType" (toJson index.val)

mutual
  partial def wasmInstructionsJson (instructions : List Instruction) : Json :=
    wasmArray (instructions.map wasmInstructionJson)

  partial def wasmInstructionJson (instruction : Instruction) : Json :=
    match instruction with
    | .Const32 value => wasmTag "CONST" (wasmTag "I32" (toJson value.val))
    | .Const64 value => wasmTag "CONST" (wasmTag "I64" (toJson value.val))
    | .LocalGet index => wasmTag "LOCAL.GET" (toJson index.val)
    | .LocalSet index => wasmTag "LOCAL.SET" (toJson index.val)
    | .LocalTee index => wasmTag "LOCAL.TEE" (toJson index.val)
    | .Nop => .str "NOP"
    | .Drop => .str "DROP"
    | .Binary value operation => wasmTag "BINOP" (wasmTag
        (match value with | .I32 => "I32" | .I64 => "I64")
        (.str (match operation with | .Add => "IAdd" | .Sub => "ISub" | .Mul => "IMul")))
    | .Block block body => wasmTag "BLOCK" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson body.val])
    | .Loop block body => wasmTag "LOOP" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson body.val])
    | .If block yes no => wasmTag "IF % % ELSE %" (wasmArray [
        wasmBlockTypeJson block, wasmInstructionsJson yes.val, wasmInstructionsJson no.val])
    | .Call index => wasmTag "CALL" (toJson index.val)
end

def wasmTypeJson (signature : FuncType) : Json :=
  wasmTag "RecT" (wasmArray [wasmTag "SubT" (wasmArray [
    .str "Final", wasmArray [], wasmTag "DefFuncT" (wasmTag "FuncT" (wasmArray [
      wasmArray (signature.parameters.val.map wasmValueTypeJson),
      wasmArray (signature.results.val.map wasmValueTypeJson)]))])])

def wasmFunctionJson (function : Function) : Json :=
  Json.mkObj [
    ("FTYPE", toJson function.type_index.val),
    ("LOCALS", wasmArray (function.locals.val.map (fun value =>
      Json.mkObj [("LTYPE", wasmValueTypeJson value)]))),
    ("BODY", wasmInstructionsJson function.body.val)]

def wasmExportJson (item : Export) : Json :=
  Json.mkObj [
    ("NAME", wasmArray (item.name.val.map (fun byte => toJson byte.val))),
    ("EDESC", wasmTag "FuncExport" (toJson item.function_index.val))]

def wasmModuleJson (module : wasm.ast.Module) : Json :=
  Json.mkObj [
    ("TYPES", wasmArray (module.types.val.map wasmTypeJson)),
    ("GLOBALS", wasmArray []), ("TABLES", wasmArray []),
    ("MEMS", wasmArray []), ("TAGS", wasmArray []),
    ("FUNCS", wasmArray (module.functions.val.map wasmFunctionJson)),
    ("START", match module.start with
      | none => .null
      | some index => Json.mkObj [("SFUNC", toJson index.val)]),
    ("ELEMS", wasmArray []), ("DATAS", wasmArray []), ("IMPORTS", wasmArray []),
    ("EXPORTS", wasmArray (module.exports.val.map wasmExportJson))]

def wasmReportJson (module : wasm.ast.Module) (choices : wasm.choices.Choices) : Json :=
  Json.mkObj [
    ("module", wasmModuleJson module),
    ("choices", wasmArray (choices.trace.val.map (fun value => toJson value.val))),
    ("state", match choices.source with | .Seeded state => toJson state.val | .Replay _ _ => .null),
    ("remaining", toJson choices.remaining.val)]

def wasmErrorMessage (error : wasm.choices.GenerationError) : String :=
  match error with
  | .InvalidConfig => "InvalidConfig: bounds or parameter+local count exceed u32"
  | .TapeExhausted offset => s!"TapeExhausted: missing choice at offset {offset.val}"
  | .ChoiceOutOfRange offset value bound =>
      s!"ChoiceOutOfRange: offset={offset.val}, value={value.val}, required value < {bound.val}"
  | .UnusedChoices consumed total => s!"UnusedChoices: consumed={consumed.val}, supplied={total.val}"
  | .WorkLimit => "WorkLimit: generation exhausted the explicit work budget"
  | .InternalInvariant => "InternalInvariant: typed builder task/choice invariant failed"

def wasmDecimal (label value : String) : IO Nat := do
  if value.isEmpty || !value.toList.all Char.isDigit then
    throw <| IO.userError s!"{label}={value} must be an unsigned decimal integer"
  match value.toNat? with
  | some number =>
      if number >= 2^64 then throw <| IO.userError s!"{label}={value} exceeds u64"
      pure number
  | none => throw <| IO.userError s!"{label}={value} could not be parsed"

def wasmUsize (value : Nat) : IO Usize :=
  match UScalar.tryMkOpt .Usize value with
  | some value => pure value
  | none => throw <| IO.userError s!"value={value} exceeds usize"

def wasmU64 (value : Nat) : IO U64 :=
  match UScalar.tryMkOpt .U64 value with
  | some value => pure value
  | none => throw <| IO.userError s!"value={value} exceeds u64"

def wasmConfig (arguments : List String) : IO wasm.Config := do
  let values ← arguments.mapM (wasmDecimal "CONFIG")
  match values with
  | [types, functions, parameters, results, locals, exports, fuel, work] =>
      if [types, functions, parameters, results, locals, exports].any (· > 64) || fuel > 128 || work > 1000000 then
        throw <| IO.userError "CLI resource limit: maxima <= 64, FUEL <= 128, WORK <= 1000000 required"
      return {
        max_types := (← wasmUsize types)
        max_functions := (← wasmUsize functions)
        max_parameters := (← wasmUsize parameters)
        max_results := (← wasmUsize results)
        max_locals := (← wasmUsize locals)
        max_exports := (← wasmUsize exports)
        fuel := (← wasmUsize fuel)
        work_limit := (← wasmU64 work) }
  | _ => throw <| IO.userError "Expected eight config fields"

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
  let config ← wasmConfig (List.replicate 7 (toString size) ++ ["100000"])
  let output ← IO.getStdout
  for index in List.range count do
    let (module, _) ← wasmUnwrap (wasm.sample config (← wasmU64 (seed + index)))
    output.putStrLn (wasmModuleJson module).compress

def wasmTape (text : String) : IO (alloc.vec.Vec U64) := do
  let cells ← if text == "-" then pure [] else (text.splitOn ",").mapM (fun cell => do
    wasmU64 (← wasmDecimal "TAPE_CELL" cell))
  if h : cells.length ≤ Usize.max then
    if cells.length > 1000000 then throw <| IO.userError "CLI resource limit: tape must have at most 1000000 cells"
    return alloc.vec.Vec.from cells h
  else throw <| IO.userError "Tape length exceeds usize"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [count, size, seed] => wasmSample (← wasmDecimal "COUNT" count) (← wasmDecimal "SIZE" size) (← wasmDecimal "SEED" seed)
  | [command, types, functions, parameters, results, locals, exports, fuel, work, input] =>
      let config ← wasmConfig [types, functions, parameters, results, locals, exports, fuel, work]
      let (module, choices) ← match command with
        | "sample" => wasmUnwrap (wasm.sample config (← wasmU64 (← wasmDecimal "SEED" input)))
        | "replay" => wasmUnwrap (wasm.replay config (← wasmTape input))
        | _ => throw <| IO.userError s!"Unknown command {command}; expected sample or replay"
      (← IO.getStdout).putStrLn (wasmReportJson module choices).compress
  | _ => throw <| IO.userError "Expected COUNT SIZE SEED, or sample/replay and eight config fields plus SEED/TAPE_CSV"
