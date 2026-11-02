import properties.wasm_module_ok.ValtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.StoragetypeValidation

def storagetypeValid (c : SpecTec.context) :
    SpecTec.storagetype → Bool
  | .ValStorageT t => ValtypeValidation.valtypeValid c t
  | .PackStorageT pt => decide (pt = .I8 ∨ pt = .I16)

theorem val_storage_success_iff
    (c : SpecTec.context) (t : SpecTec.valtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Storagetype_ok c (.ValStorageT t)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c t⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Storagetype_ok_clauses c (.ValStorageT t))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Storagetype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Storagetype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard
          cases htail with
          | bind_success hval hpure =>
            rename_i _ value
            cases value
            cases hpure
            exact hval
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«Storagetype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:storagetype:PackStorageT»] at hcond
        | next _ hnone => cases hnone
  · intro hval
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Storagetype_ok_clauses c (.ValStorageT t)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Storagetype_ok:clause:0» c (.ValStorageT t))
      n (.success (.of ())) finish
    unfold SpecTec.«Storagetype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success hval
      exact SpecTecExecution.Eval.pure ()

theorem pack_storage_success_iff
    (c : SpecTec.context) (pt : SpecTec.packtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Storagetype_ok c (.PackStorageT pt)⟩)
      n (.success (.of ())) finish ↔
    (pt = .I8 ∨ pt = .I16) ∧ finish = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Storagetype_ok_clauses c (.PackStorageT pt))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Storagetype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Storagetype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:storagetype:ValStorageT»] at hcond
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«Storagetype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard
            cases htail with
            | bind_success hpack hpure =>
              cases hpack with
              | guard_true hallowed =>
                cases hpure
                exact ⟨by simpa using hallowed, rfl⟩
        | next _ hnone => cases hnone
  · rintro ⟨hallowed, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Storagetype_ok_clauses c (.PackStorageT pt)))
      finish (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Storagetype_ok:clause:0» c (.PackStorageT pt))
        finish .unmatch finish
      unfold SpecTec.«Storagetype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:storagetype:ValStorageT»]
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Storagetype_ok:clause:1» c (.PackStorageT pt))
        finish (.success (.of ())) finish
      unfold SpecTec.«Storagetype_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          simpa using hallowed
        · exact SpecTecExecution.Eval.pure ()

theorem storagetype_success_iff_valid
    (c : SpecTec.context) (zt : SpecTec.storagetype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Storagetype_ok c zt⟩)
      n (.success (.of ())) finish ↔
    storagetypeValid c zt = true ∧ finish = n := by
  cases zt with
  | ValStorageT t =>
    rw [val_storage_success_iff,
      ValtypeValidation.valtype_success_iff_valid]
    rfl
  | PackStorageT pt =>
    rw [pack_storage_success_iff]
    simp [storagetypeValid]

end properties.wasm_module_ok.StoragetypeValidation
