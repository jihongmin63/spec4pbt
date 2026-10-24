import properties.wasm_module_not_ok.HeaptypeListRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollSubtype (st : SpecTec.subtype) (x y : Nat) : SpecTec.subtype :=
  match st with
  | .SubT fin hts strt =>
      .SubT fin (rollHeaptypes hts x y) (rollStrtype strt x y)

theorem subst_subtype_roll_total (st : SpecTec.subtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» st⟩)
      start (.success (.of (rollSubtype st x y))) start := by
  cases st with
  | SubT fin hts strt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_subtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.SubT fin hts strt)) ())
        start (.success (.of (rollSubtype (.SubT fin hts strt) x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_subtype:clause:0» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.SubT fin hts strt))
        start (.success (.of (rollSubtype (.SubT fin hts strt) x y))) start
      unfold SpecTec.«$subst_subtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_heaptype_list_roll_total hts x y start)
      apply SpecTecExecution.Eval.bind_success
        (subst_strtype_roll_total strt x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.subtype.SubT fin
          (rollHeaptypes hts x y) (rollStrtype strt x y))

theorem subst_subtype_roll_deterministic (st : SpecTec.subtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» st⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollSubtype st x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_subtype_roll_total st x y start)

end properties.wasm_module_not_ok.Rejection
