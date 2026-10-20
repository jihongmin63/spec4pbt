import pbt.example.Generator

/-! Draw Palamedes samples and export their numeric values as JSON lines. -/

private def parseNat (name value : String) : IO Nat :=
  match value.toNat? with
  | some result => pure result
  | none => throw (IO.userError s!"{name} must be a natural number; received {value}")

private def emit (count size : Nat) : IO Unit := do
  if size == 0 then
    throw (IO.userError "size must be positive for the indexed natural generator")
  let config : SampleConfig := { sizeLimit := size, backtrackLimit := 100, sizeRetryLimit := 100 }
  for index in [:count] do
    let input ← _root_.sample Example.generate config
    IO.println s!"\{\"index\":{index},\"size\":{size},\"input\":{input}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [countText, sizeText] =>
    let count ← parseNat "count" countText
    let size ← parseNat "size" sizeText
    emit count size
    pure 0
  | _ => throw (IO.userError "usage: example-samples COUNT SIZE")
