import properties.wasm_module_ok.MatchHeaptypeBasic
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRangeExact

/-- The translated range call used by `Rectype_ok` computes the canonical
index list without consuming fresh-value supply. -/
theorem range_success_iff
    (k : Nat) (ns : List Nat) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List Nat, SpecTec.Call.«$range» k⟩)
      start (.success (.of ns)) finish ↔
    ns = List.range k ∧ finish = start := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (properties.wasm_module_ok.MatchHeaptypeBasic.range_total k start)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact properties.wasm_module_ok.MatchHeaptypeBasic.range_total k finish

end properties.wasm_module_ok.CandidateRangeExact
