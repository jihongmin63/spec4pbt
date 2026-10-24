import properties.wasm_module_not_ok.StorageRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollFieldtypes (ts : List SpecTec.fieldtype) (x y : Nat) :
    List SpecTec.fieldtype :=
  ts.map (fun t => rollFieldtype t x y)

theorem subst_fieldtype_list_roll_total (ts : List SpecTec.fieldtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.fieldtype,
        SpecTec.SpecTecCall.«$subst_structtype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» ts⟩)
      start (.success (.of (rollFieldtypes ts x y))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» []) ())
        start (.success (.of (rollFieldtypes [] x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
          (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» [])
        start (.success (.of (rollFieldtypes [] x y))) start
      simpa [SpecTec.«$subst_structtype:case_1:iter:0:clause:0»,
        rollFieldtypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.fieldtype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» (t :: ts)) ())
        start (.success (.of (rollFieldtypes (t :: ts) x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
            (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
            (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» (t :: ts))
          start (.success (.of (rollFieldtypes (t :: ts) x y))) start
        unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_fieldtype_roll_total t x y start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [rollFieldtypes] using
          (SpecTecExecution.Eval.pure
            (rollFieldtype t x y :: rollFieldtypes ts x y) (n := start))

theorem subst_fieldtype_list_roll_deterministic (ts : List SpecTec.fieldtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.fieldtype,
        SpecTec.SpecTecCall.«$subst_structtype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.SpecTecCall.«$s_roll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollFieldtypes ts x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_fieldtype_list_roll_total ts x y start)

end properties.wasm_module_not_ok.Rejection
