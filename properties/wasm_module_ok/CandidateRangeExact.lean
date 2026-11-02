import properties.wasm_module_ok.MatchHeaptypeBasic

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRangeExact

/-- The translated range call used by `Rectype_ok` computes the canonical
index list without consuming fresh-value supply. -/
theorem range_success_iff
    (k : Nat) (ns : List Nat) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» k⟩)
      start (.success (.of ns)) finish ↔
    ns = List.range k ∧ finish = start := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (properties.wasm_module_ok.MatchHeaptypeBasic.range_total k start)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact properties.wasm_module_ok.MatchHeaptypeBasic.range_total k finish

end properties.wasm_module_ok.CandidateRangeExact
