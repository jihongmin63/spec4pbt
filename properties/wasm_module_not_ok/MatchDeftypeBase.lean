import properties.wasm_module_not_ok.Rejection

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_deftype_equal_total (d : List SpecTec.deftype)
    (dt : SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt dt⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_deftype_clauses» d dt dt) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_deftype:clause:0» d dt dt)
    start (.success (.of true)) start
  unfold SpecTec.«$match_deftype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure true

theorem match_deftype_equal_deterministic (d : List SpecTec.deftype)
    (dt : SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt dt⟩)
      start outcome finalSupply) :
    outcome = .success (.of true) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_deftype_equal_total d dt start)

end properties.wasm_module_not_ok.Rejection
