import properties.wasm_module_not_ok.HeaptypeRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollReftype (rt : SpecTec.reftype) (x y : Nat) : SpecTec.reftype :=
  match rt with
  | .«% %» null ht => .«% %» null (rollHeaptype ht x y)

theorem subst_reftype_roll_total (rt : SpecTec.reftype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype,
        SpecTec.SpecTecCall.«$subst_reftype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» rt⟩)
      start (.success (.of (rollReftype rt x y))) start := by
  cases rt with
  | «% %» null ht =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_reftype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.«% %» null ht)) ())
        start (.success (.of (rollReftype (.«% %» null ht) x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_reftype:clause:0» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.«% %» null ht))
        start (.success (.of (rollReftype (.«% %» null ht) x y))) start
      unfold SpecTec.«$subst_reftype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_heaptype_roll_total ht x y start)
      simpa [rollReftype] using
        (SpecTecExecution.Eval.pure
          (SpecTec.reftype.«% %» null (rollHeaptype ht x y)) (n := start))

theorem subst_reftype_roll_deterministic (rt : SpecTec.reftype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype,
        SpecTec.SpecTecCall.«$subst_reftype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» rt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollReftype rt x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_reftype_roll_total rt x y start)

end properties.wasm_module_not_ok.Rejection
