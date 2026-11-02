import properties.wasm_module_ok.DefaultableValidation
import properties.wasm_module_ok.ValtypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.LocalValidation

def localType (l : SpecTec.«local») : SpecTec.localtype :=
  if DefaultableValidation.defaultable l.LTYPE then
    .LocalT .Set l.LTYPE
  else
    .LocalT .Unset l.LTYPE

theorem local_of_valtype_success
    (c : SpecTec.context) (l : SpecTec.«local»)
    (n finalSupply : Nat)
    (hval : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c l.LTYPE⟩)
      n (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.localtype, SpecTec.Call.Local_ok c l⟩)
      n (.success (.of (localType l))) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Local_ok_clauses c l))
    n (.success (.of (localType l))) finalSupply
  cases hdef : DefaultableValidation.defaultable l.LTYPE with
  | true =>
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Local_ok:clause:0» c l)
      n (.success (.of (localType l))) finalSupply
    unfold SpecTec.«Local_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hval
    apply SpecTecExecution.Eval.bind_success
      (DefaultableValidation.defaultable_total l.LTYPE finalSupply)
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      simp [hdef]
    · simpa [localType, hdef] using
        (SpecTecExecution.Eval.pure
          (SpecTec.localtype.LocalT .Set l.LTYPE))
  | false =>
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Local_ok:clause:0» c l)
        n .unmatch finalSupply
      unfold SpecTec.«Local_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success hval
      apply SpecTecExecution.Eval.bind_success
        (DefaultableValidation.defaultable_total l.LTYPE finalSupply)
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [hdef]
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Local_ok:clause:1» c l)
        n (.success (.of (localType l))) finalSupply
      unfold SpecTec.«Local_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success hval
      apply SpecTecExecution.Eval.bind_success
        (DefaultableValidation.defaultable_total l.LTYPE finalSupply)
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        simp [hdef]
      · simpa [localType, hdef] using
          (SpecTecExecution.Eval.pure
            (SpecTec.localtype.LocalT .Unset l.LTYPE))

theorem local_success_inv_valtype
    (c : SpecTec.context) (l : SpecTec.«local»)
    (result : SpecTec.localtype) (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.localtype, SpecTec.Call.Local_ok c l⟩)
      n (.success (.of result)) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Valtype_ok c l.LTYPE⟩)
        n (.success (.of ())) middle := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Local_ok:clause:0» c l)
        (fun _ => SpecTecExecution.tryClauses
          [fun _ => SpecTec.«Local_ok:clause:1» c l]))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Local_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hval _ => exact ⟨_, hval⟩
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Local_ok:clause:1» c l)
          (fun _ => .unmatch))
        n (.success (.of result)) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Local_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success hval _ => exact ⟨_, hval⟩
      | orElse_unmatch _ hlast => cases hlast

theorem local_success_iff
    (c : SpecTec.context) (l : SpecTec.«local»)
    (result : SpecTec.localtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.localtype, SpecTec.Call.Local_ok c l⟩)
      n (.success (.of result)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c l.LTYPE⟩)
      n (.success (.of ())) finalSupply ∧
    result = localType l := by
  constructor
  · intro h
    obtain ⟨middle, hval⟩ :=
      local_success_inv_valtype c l result n finalSupply h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (local_of_valtype_success c l n middle hval)
    cases hout
    cases hsupply
    exact ⟨hval, rfl⟩
  · rintro ⟨hval, rfl⟩
    exact local_of_valtype_success c l n finalSupply hval

theorem local_success_iff_valid
    (c : SpecTec.context) (l : SpecTec.«local»)
    (result : SpecTec.localtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.localtype, SpecTec.Call.Local_ok c l⟩)
      n (.success (.of result)) finalSupply ↔
    ValtypeValidation.valtypeValid c l.LTYPE = true ∧
    result = localType l ∧ finalSupply = n := by
  rw [local_success_iff, ValtypeValidation.valtype_success_iff_valid]
  constructor
  · rintro ⟨⟨hvalid, hsupply⟩, hresult⟩
    exact ⟨hvalid, hresult, hsupply⟩
  · rintro ⟨hvalid, hresult, hsupply⟩
    exact ⟨⟨hvalid, hsupply⟩, hresult⟩

end properties.wasm_module_ok.LocalValidation
