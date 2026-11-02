import properties.wasm_module_ok.ValtypeTotal
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.GlobaltypeValidation

def globaltypeValid (c : SpecTec.context) : SpecTec.globaltype → Bool
  | .GlobalT _ t => ValtypeValidation.valtypeValid c t

theorem globaltype_success_iff_valid (c : SpecTec.context)
    (gt : SpecTec.globaltype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Globaltype_ok c gt⟩)
      n (.success (.of ())) finalSupply ↔
    globaltypeValid c gt = true ∧ finalSupply = n := by
  cases gt with
  | GlobalT mutation t =>
    constructor
    · intro h
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Globaltype_ok:clause:0» c (.GlobalT mutation t))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at hbody
        cases hbody with
        | orElse_success hclause =>
          unfold SpecTec.«Globaltype_ok:clause:0» at hclause
          cases hclause with
          | bind_success hval hpure =>
            cases hpure with
            | pure =>
              simpa [globaltypeValid] using
                (ValtypeValidation.valtype_success_iff_valid
                  c t n finalSupply).1 hval
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
    · rintro ⟨hv, rfl⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Globaltype_ok_clauses c (.GlobalT mutation t)))
        finalSupply (.success (.of ())) finalSupply
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Globaltype_ok:clause:0» c (.GlobalT mutation t))
        finalSupply (.success (.of ())) finalSupply
      unfold SpecTec.«Globaltype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact (ValtypeValidation.valtype_success_iff_valid
          c t finalSupply finalSupply).2 ⟨hv, rfl⟩
      · exact SpecTecExecution.Eval.pure ()

def globaltypeOutcome (c : SpecTec.context) (gt : SpecTec.globaltype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if globaltypeValid c gt then .success (.of ()) else .unmatch

theorem globaltype_total (c : SpecTec.context)
    (gt : SpecTec.globaltype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Globaltype_ok c gt⟩)
      n (globaltypeOutcome c gt) n := by
  cases gt with
  | GlobalT mutation t =>
    cases hv : ValtypeValidation.valtypeValid c t with
    | true =>
      simpa [globaltypeOutcome, globaltypeValid, hv] using
        (globaltype_success_iff_valid
          c (.GlobalT mutation t) n n).2 ⟨hv, rfl⟩
    | false =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Globaltype_ok_clauses c (.GlobalT mutation t)))
        n (globaltypeOutcome c (.GlobalT mutation t)) n
      simp only [globaltypeOutcome, globaltypeValid, hv]
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Globaltype_ok:clause:0» c (.GlobalT mutation t))
          n .unmatch n
        unfold SpecTec.«Globaltype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        simpa [ValtypeTotal.valtypeOutcome, hv] using
          ValtypeTotal.valtype_total c t n
      · exact SpecTecExecution.tryClauses_nil n

end properties.wasm_module_ok.GlobaltypeValidation
