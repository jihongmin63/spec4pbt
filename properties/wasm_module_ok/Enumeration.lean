import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_not_ok.TypeFamilyCodec
import Mathlib.Logic.Equiv.List

set_option autoImplicit false

namespace properties.wasm_module_ok.Enumeration

def decodeCandidates {α : Type} [Encodable α] (n : Nat) : List α :=
  (List.range (n + 1)).filterMap (Encodable.decode (α := α))

theorem decodeCandidates_mono {α : Type} [Encodable α]
    (n k : Nat) (a : α) :
    a ∈ decodeCandidates n → a ∈ decodeCandidates (n + k) := by
  simp only [decodeCandidates, List.mem_filterMap, List.mem_range]
  rintro ⟨code, hcode, hdecode⟩
  exact ⟨code, by omega, hdecode⟩

theorem decodeCandidates_complete {α : Type} [Encodable α]
    (a : α) : ∃ n : Nat, a ∈ decodeCandidates n := by
  refine ⟨Encodable.encode a, ?_⟩
  simp only [decodeCandidates, List.mem_filterMap, List.mem_range]
  exact ⟨Encodable.encode a, Nat.lt_succ_self _, Encodable.encodek a⟩

theorem fmag_roundtrip (x : SpecTec.fmag) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem set_roundtrip {α : Type} [Encodable α] (x : SpecTec.set α) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem vecop_roundtrip {α : Type} [Encodable α] (x : SpecTec.vecop α) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem export_roundtrip (x : SpecTec.«export») :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

end properties.wasm_module_ok.Enumeration
