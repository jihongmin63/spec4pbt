import GeneratorRust
import Lean

open Lean Aeneas.Std generator_rust

/-- JSON serialization is outside the translated generator's extraction boundary. -/
def expressionJson (expression : ast.Expr) : Lean.Json :=
  let tagged (tag : String) (fields : List Lean.Json) : Lean.Json :=
    .arr ((.str tag :: fields).toArray)
  match expression with
  | .Int value => tagged "int" [toJson value.val]
  | .Bool value => tagged "bool" [toJson value]
  | .Var index => tagged "var" [toJson index.val]
  | .Neg child => tagged "neg" [expressionJson child]
  | .Not child => tagged "not" [expressionJson child]
  | .Add left right => tagged "add" [expressionJson left, expressionJson right]
  | .Eq left right => tagged "eq" [expressionJson left, expressionJson right]
  | .If condition yes no =>
    tagged "if" [expressionJson condition, expressionJson yes, expressionJson no]
  | .Let binder rhs body =>
    let typeLabel := match binder with | .Int => "int" | .Boolean => "bool"
    tagged "let" [toJson typeLabel, expressionJson rhs, expressionJson body]

/-- Parse protocol integers before constructing bounded Aeneas scalar values. -/
def decimal (label value : String) : IO Nat := do
  if value.isEmpty || !value.toList.all Char.isDigit then
    throw <| IO.userError s!"{label}={value} must be an unsigned decimal integer"
  match value.toNat? with
  | some number => pure number
  | none => throw <| IO.userError s!"{label}={value} could not be parsed as a natural number"

/-- Invoke the generated function and expose its complete AST and final RNG state. -/
def sample (count nodes seed : Nat) : IO Unit := do
  if count == 0 || nodes == 0 || nodes > 1024 then
    throw <| IO.userError s!"COUNT={count} must be positive; NODES={nodes} must be in 1..1024"
  if count * nodes >= 2^64 then
    throw <| IO.userError s!"COUNT={count} times NODES={nodes} exceeds u64"
  if seed + count - 1 >= 2^64 then
    throw <| IO.userError s!"SEED={seed} plus COUNT={count} minus one exceeds u64"
  let nodeCount ← match UScalar.tryMkOpt .Usize nodes with
    | some value => pure value
    | none => throw <| IO.userError s!"NODES={nodes} exceeds usize"
  let output ← IO.getStdout
  for index in List.range count do
    let valueType := if index % 2 == 0 then ast.ValueType.Int else ast.ValueType.Boolean
    let typeName := if index % 2 == 0 then "int" else "bool"
    let state ← match UScalar.tryMkOpt .U64 (seed + index) with
      | some value => pure value
      | none => throw <| IO.userError s!"Per-sample seed={seed + index} exceeds u64"
    let result := generator.generate valueType nodeCount (Slice.from [] (Nat.zero_le _)) state
    match result.match with
    | .ok (expression, nextState) =>
      let record := Lean.Json.mkObj [
        ("index", toJson index), ("type", toJson typeName),
        ("expr", expressionJson expression), ("state", toJson nextState.val)]
      output.putStrLn record.compress
    | .vis (.fail error) _ =>
      throw <| IO.userError s!"Translated generator failed: index={index}, nodes={nodes}, seed={seed + index}, error={repr error}"
    | .div => throw <| IO.userError s!"Translated generator diverged: index={index}, nodes={nodes}, seed={seed + index}"

/-- Executable protocol wrapper; the generator body is entirely tool generated. -/
def main (arguments : List String) : IO Unit := do
  match arguments with
  | [count, nodes, seed] => sample (← decimal "COUNT" count) (← decimal "NODES" nodes) (← decimal "SEED" seed)
  | _ => throw <| IO.userError s!"Expected COUNT NODES SEED; received {arguments.length} arguments"
