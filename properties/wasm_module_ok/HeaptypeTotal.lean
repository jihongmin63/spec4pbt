import properties.wasm_module_ok.HeaptypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.HeaptypeTotal

open HeaptypeValidation

theorem heaptype_invalid_unmatch (c : SpecTec.context)
    (ht : SpecTec.heaptype) (n : Nat)
    (hvalid : heaptypeValid c ht = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c ht⟩)
      n .unmatch n := by
  have hnotbase : ht ∉ baseHeaptypes := by
    intro hb
    have hv : heaptypeValid c ht = true :=
      (heaptype_valid_iff c ht).2 (Or.inl hb)
    rw [hvalid] at hv
    cases hv
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Heaptype_ok_clauses c ht) ())
    n .unmatch n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Heaptype_ok:clause:0» c ht) n .unmatch n
    unfold SpecTec.«Heaptype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simpa [baseHeaptypes] using hnotbase
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Heaptype_ok:clause:1» c ht) n .unmatch n
      cases ht with
      | VarHT tv =>
        unfold SpecTec.«Heaptype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · cases tv with
          | RecX x =>
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            change ¬ false = true
            decide
          | StatX x =>
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · apply SpecTecExecution.Eval.bind_unmatch
              apply SpecTecExecution.Eval.guard_false
              have hbound : ¬ x < c.TYPES.length := by
                simpa [heaptypeValid] using hvalid
              intro h
              exact hbound h.2
      | DefHT dt =>
        unfold SpecTec.«Heaptype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        change ¬ false = true
        decide
      | AnyHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | NoneHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | EqHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | I31HT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | StructHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | ArrayHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | FuncHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | NoFuncHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | ExnHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | NoExnHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | ExternHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | NoExternHT => exact (hnotbase (by simp [baseHeaptypes])).elim
      | BotHT => exact (hnotbase (by simp [baseHeaptypes])).elim
    · exact SpecTecExecution.firstSuccess_nil () n

def heaptypeOutcome (c : SpecTec.context) (ht : SpecTec.heaptype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if heaptypeValid c ht then .success (.of ()) else .unmatch

theorem heaptype_total (c : SpecTec.context)
    (ht : SpecTec.heaptype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c ht⟩)
      n (heaptypeOutcome c ht) n := by
  cases hv : heaptypeValid c ht with
  | false =>
    simpa [heaptypeOutcome, hv] using
      heaptype_invalid_unmatch c ht n hv
  | true =>
    simpa [heaptypeOutcome, hv] using
      (heaptype_success_iff_valid c ht n n).2 ⟨hv, rfl⟩

end properties.wasm_module_ok.HeaptypeTotal
