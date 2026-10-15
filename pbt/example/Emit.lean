import pbt.example.Generator

/-!
The executable bridge exports proof-carrying Lean samples as JSON lines for the
Python source renderer. Proofs remain in Lean; only the numeric input is exported.
-/

private def parseNat (name value : String) : IO Nat :=
  match value.toNat? with
  | some result => pure result
  | none => throw (IO.userError s!"{name} must be a natural number; received {value}")

private def emit (count size seed : Nat) : IO Unit := do
  for index in [:count] do
    let sampleSeed := seed + index
    let input := Example.generate size sampleSeed
    IO.println s!"\{\"index\":{index},\"size\":{size},\"seed\":{sampleSeed},\"input\":{input}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [countText, sizeText, seedText] =>
    let count ← parseNat "count" countText
    let size ← parseNat "size" sizeText
    let seed ← parseNat "seed" seedText
    emit count size seed
    pure 0
  | _ => throw (IO.userError "usage: example-samples COUNT SIZE SEED")
