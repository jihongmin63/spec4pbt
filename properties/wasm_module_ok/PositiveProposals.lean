/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveCheck
import Palamedes.Data.Nat
namespace properties.wasm_module_ok.PositiveProposals

/-- These productive proposals supplement the complete full-syntax fallback.
Their limited shapes do not restrict the final generator's support. -/
def emptyModule : SpecTec.module := ⟨[], [], [], [], [], [], none, [], [], [], []⟩

def memoryModules : Gen SpecTec.module := do
  let addr ← Gen.pick (pure SpecTec.addrtype.I32AT) (pure .I64AT)
  let bound := if addr = .I32AT then 65536 else 281474976710656
  let rawMin ← Gen.pick (pure 0) (Gen.pick (pure bound) Gen.arbNat)
  let lo := rawMin % (bound + 1)
  let width ← Gen.arbNat
  let hi ← Gen.pick (pure none) (pure (some (lo + width % (bound + 1 - lo))))
  let count ← Gen.pick (pure 1) (Gen.pick (pure 2) (pure 3))
  pure { emptyModule with
    MEMS := List.replicate count ⟨.MemoryT addr ⟨lo, hi⟩⟩
    EXPORTS := (List.range count).map (fun i => ⟨[109, 48 + i], .MemExport i⟩) }

def functionModule (count : Nat) (body : List SpecTec.instr) : SpecTec.module :=
  { emptyModule with
    TYPES := [.RecT [.SubT .Final [] (.DefFuncT (.FuncT [] []))]]
    FUNCS := List.replicate count ⟨0, [], body⟩
    START := some ⟨0⟩
    EXPORTS := (List.range count).map (fun i => ⟨[102, 48 + i], .FuncExport i⟩) }

def functionModules : Gen SpecTec.module := do
  let n ← Gen.arbNat
  let body ← Gen.pick (pure (List.replicate (n % 8) SpecTec.instr.NOP))
    (pure (SpecTec.instr.UNREACHABLE :: List.replicate (n % 8) SpecTec.instr.NOP))
  let count ← Gen.pick (pure 1) (Gen.pick (pure 2) (pure 3))
  pure (functionModule count body)

def modules : Gen SpecTec.module := Gen.pick memoryModules functionModules

end properties.wasm_module_ok.PositiveProposals
