import properties.wasm_module_ok.HeaptypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReftypeTotal

def reftypeValid (c : SpecTec.context) : SpecTec.reftype → Bool
  | .«% %» _ ht => HeaptypeValidation.heaptypeValid c ht

def reftypeOutcome (c : SpecTec.context) (rt : SpecTec.reftype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if reftypeValid c rt then .success (.of ()) else .unmatch

theorem reftype_total (c : SpecTec.context)
    (rt : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Reftype_ok c rt⟩)
      n (reftypeOutcome c rt) n := by
  cases rt with
  | «% %» nullable ht =>
    cases hv : HeaptypeValidation.heaptypeValid c ht with
    | true =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Reftype_ok_clauses c (.«% %» nullable ht)) ())
        n (reftypeOutcome c (.«% %» nullable ht)) n
      simp only [reftypeOutcome, reftypeValid, hv, ite_true]
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Reftype_ok:clause:0» c (.«% %» nullable ht))
        n (.success (.of ())) n
      unfold SpecTec.«Reftype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · simpa [HeaptypeTotal.heaptypeOutcome, hv] using
          HeaptypeTotal.heaptype_total c ht n
      · exact SpecTecExecution.Eval.pure ()
    | false =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Reftype_ok_clauses c (.«% %» nullable ht)) ())
        n (reftypeOutcome c (.«% %» nullable ht)) n
      simp only [reftypeOutcome, reftypeValid, hv]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Reftype_ok:clause:0» c (.«% %» nullable ht))
          n .unmatch n
        unfold SpecTec.«Reftype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        simpa [HeaptypeTotal.heaptypeOutcome, hv] using
          HeaptypeTotal.heaptype_total c ht n
      · exact SpecTecExecution.firstSuccess_nil () n

theorem reftype_success_iff_valid (c : SpecTec.context)
    (rt : SpecTec.reftype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Reftype_ok c rt⟩)
      n (.success (.of ())) finalSupply ↔
    reftypeValid c rt = true ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (reftype_total c rt n)
    cases hv : reftypeValid c rt with
    | true => exact ⟨rfl, hsupply⟩
    | false => simp [reftypeOutcome, hv] at hout
  · rintro ⟨hv, rfl⟩
    simpa [reftypeOutcome, hv] using reftype_total c rt finalSupply

end properties.wasm_module_ok.ReftypeTotal
