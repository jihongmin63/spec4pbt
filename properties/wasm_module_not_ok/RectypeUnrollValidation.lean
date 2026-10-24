import properties.wasm_module_not_ok.SubtypeListUnrollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollRectype (sourceRect envRect : SpecTec.rectype) : SpecTec.rectype :=
  match sourceRect with
  | .RecT sts => .RecT (unrollSubtypes sts envRect)

theorem subst_rectype_unroll_total (sourceRect envRect : SpecTec.rectype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype» SpecTec.rectype envRect
          SpecTec.SpecTecCall.«$s_unroll» sourceRect⟩)
      start (.success (.of (unrollRectype sourceRect envRect))) start := by
  cases sourceRect with
  | RecT sts =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_rectype_clauses» SpecTec.rectype envRect
            SpecTec.SpecTecCall.«$s_unroll» (.RecT sts)) ())
        start (.success (.of (unrollRectype (.RecT sts) envRect))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_rectype:clause:0» SpecTec.rectype envRect
          SpecTec.SpecTecCall.«$s_unroll» (.RecT sts))
        start (.success (.of (unrollRectype (.RecT sts) envRect))) start
      unfold SpecTec.«$subst_rectype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_subtype_list_unroll_total sts envRect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.rectype.RecT (unrollSubtypes sts envRect))

theorem subst_rectype_unroll_deterministic
    (sourceRect envRect : SpecTec.rectype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype» SpecTec.rectype envRect
          SpecTec.SpecTecCall.«$s_unroll» sourceRect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollRectype sourceRect envRect)) ∧
      finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_rectype_unroll_total sourceRect envRect start)

theorem unrollrt_total (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype, SpecTec.SpecTecCall.«$unrollrt» rect⟩)
      start (.success (.of (unrollRectype rect rect))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$unrollrt_clauses» rect) ())
    start (.success (.of (unrollRectype rect rect))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$unrollrt:clause:0» rect)
    start (.success (.of (unrollRectype rect rect))) start
  unfold SpecTec.«$unrollrt:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (subst_rectype_unroll_total rect rect start)
  exact SpecTecExecution.Eval.pure (unrollRectype rect rect)

theorem unrollrt_deterministic (rect : SpecTec.rectype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype, SpecTec.SpecTecCall.«$unrollrt» rect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollRectype rect rect)) ∧
      finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (unrollrt_total rect start)

end properties.wasm_module_not_ok.Rejection
