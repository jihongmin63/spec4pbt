import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchPrimitiveValidation

theorem match_numtype_total (dts : List SpecTec.deftype)
    (a b : SpecTec.numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_numtype» dts a b⟩)
      n (.success (.of (decide (b = a)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_numtype_clauses» dts a b) ())
    n (.success (.of (decide (b = a)))) n
  by_cases heq : b = a
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_numtype:clause:0» dts a b)
      n (.success (.of (decide (b = a)))) n
    unfold SpecTec.«$match_numtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true heq
    · simpa [heq] using (SpecTecExecution.Eval.pure true (n := n))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_numtype:clause:0» dts a b) n .unmatch n
      unfold SpecTec.«$match_numtype:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false heq)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_numtype:clause:1» dts a b)
        n (.success (.of (decide (b = a)))) n
      simpa [SpecTec.«$match_numtype:clause:1», heq] using
        (SpecTecExecution.Eval.pure false (n := n))

theorem match_vectype_total (dts : List SpecTec.deftype)
    (a b : SpecTec.vectype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_vectype» dts a b⟩)
      n (.success (.of (decide (a = b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_vectype_clauses» dts a b) ())
    n (.success (.of (decide (a = b)))) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_numtype_success_iff (dts : List SpecTec.deftype)
    (a b : SpecTec.numtype) (result : Bool)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_numtype» dts a b⟩)
      n (.success (.of result)) finalSupply ↔
    result = decide (b = a) ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (match_numtype_total dts a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_numtype_total dts a b finalSupply

theorem match_vectype_success_iff (dts : List SpecTec.deftype)
    (a b : SpecTec.vectype) (result : Bool)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_vectype» dts a b⟩)
      n (.success (.of result)) finalSupply ↔
    result = decide (a = b) ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (match_vectype_total dts a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_vectype_total dts a b finalSupply

end properties.wasm_module_ok.MatchPrimitiveValidation
