import properties.wasm_module_not_ok.RolldtValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

/-- The computable completed outcome of the generated `$subst_of` relation. -/
def substOfOutcome (tv : SpecTec.typevar) (dts : List SpecTec.deftype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match tv with
  | .StatX n =>
      match dts[n]? with
      | some dt => .success (.of (SpecTec.heaptype.DefHT dt))
      | none => .unmatch
  | .RecX n => .success (.of (SpecTec.heaptype.VarHT (.RecX n)))

private theorem subst_of_stat_some (n start : Nat)
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (hget : dts[n]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_of» (.StatX n) dts⟩)
      start (.success (.of (SpecTec.heaptype.DefHT dt))) start := by
  have hbound : n < dts.length := by
    by_contra h
    have hnone : dts[n]? = none := List.getElem?_eq_none (Nat.le_of_not_gt h)
    rw [hget] at hnone
    cases hnone
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_of_clauses» (.StatX n) dts) ())
    start (.success (.of (SpecTec.heaptype.DefHT dt))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$subst_of:clause:0» (.StatX n) dts)
    start (.success (.of (SpecTec.heaptype.DefHT dt))) start
  unfold SpecTec.«$subst_of:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (by simp [SpecTec.«exec:match:typevar:StatX»])
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hbound
    · rw [hget]
      exact SpecTecExecution.Eval.pure (SpecTec.heaptype.DefHT dt)

private theorem subst_of_stat_none (n start : Nat)
    (dts : List SpecTec.deftype) (hget : dts[n]? = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_of» (.StatX n) dts⟩)
      start .unmatch start := by
  have hbound : ¬ n < dts.length := by
    have hle : dts.length ≤ n := List.getElem?_eq_none_iff.mp hget
    omega
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_of_clauses» (.StatX n) dts) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_of:clause:0» (.StatX n) dts) start .unmatch start
    unfold SpecTec.«$subst_of:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:typevar:StatX»])
    · apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false hbound
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_of:clause:1» (.StatX n) dts) start .unmatch start
      unfold SpecTec.«$subst_of:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:typevar:RecX»])
    · exact SpecTecExecution.firstSuccess_nil () start

private theorem subst_of_rec (n start : Nat)
    (dts : List SpecTec.deftype) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_of» (.RecX n) dts⟩)
      start (.success (.of (SpecTec.heaptype.VarHT (.RecX n)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_of_clauses» (.RecX n) dts) ())
    start (.success (.of (SpecTec.heaptype.VarHT (.RecX n)))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_of:clause:0» (.RecX n) dts) start .unmatch start
    unfold SpecTec.«$subst_of:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:typevar:StatX»])
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_of:clause:1» (.RecX n) dts)
      start (.success (.of (SpecTec.heaptype.VarHT (.RecX n)))) start
    unfold SpecTec.«$subst_of:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:typevar:RecX»])
    · exact SpecTecExecution.Eval.pure
        (SpecTec.heaptype.VarHT (.RecX n))

theorem subst_of_total (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_of» tv dts⟩)
      start (substOfOutcome tv dts) start := by
  cases tv with
  | RecX n => exact subst_of_rec n start dts
  | StatX n =>
      cases hget : dts[n]? with
      | none =>
          simpa [substOfOutcome, hget] using subst_of_stat_none n start dts hget
      | some dt =>
          simpa [substOfOutcome, hget] using subst_of_stat_some n start dts dt hget

theorem subst_of_deterministic (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_of» tv dts⟩)
      start outcome finalSupply) :
    outcome = substOfOutcome tv dts ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_of_total tv dts start)

end properties.wasm_module_not_ok.Rejection
