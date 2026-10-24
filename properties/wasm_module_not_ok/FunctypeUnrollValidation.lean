import properties.wasm_module_not_ok.ValtypeListUnrollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem subst_resulttype_unroll_total (ts : SpecTec.resulttype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.resulttype,
        SpecTec.SpecTecCall.«$subst_resulttype» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» ts⟩)
      start (.success (.of (unrollValtypes ts rect))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_resulttype_clauses» SpecTec.rectype rect
        SpecTec.SpecTecCall.«$s_unroll» ts) ())
    start (.success (.of (unrollValtypes ts rect))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$subst_resulttype:clause:0» SpecTec.rectype rect
      SpecTec.SpecTecCall.«$s_unroll» ts)
    start (.success (.of (unrollValtypes ts rect))) start
  unfold SpecTec.«$subst_resulttype:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (subst_valtype_list_unroll_total ts rect start)
  exact SpecTecExecution.Eval.pure (unrollValtypes ts rect)

def unrollFunctype (ft : SpecTec.functype) (rect : SpecTec.rectype) : SpecTec.functype :=
  match ft with
  | .FuncT params results =>
      .FuncT (unrollValtypes params rect) (unrollValtypes results rect)

theorem subst_functype_unroll_total (ft : SpecTec.functype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.functype,
        SpecTec.SpecTecCall.«$subst_functype» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» ft⟩)
      start (.success (.of (unrollFunctype ft rect))) start := by
  cases ft with
  | FuncT params results =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_functype_clauses» SpecTec.rectype rect
            SpecTec.SpecTecCall.«$s_unroll» (.FuncT params results)) ())
        start (.success (.of
          (unrollFunctype (.FuncT params results) rect))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_functype:clause:0» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» (.FuncT params results))
        start (.success (.of
          (unrollFunctype (.FuncT params results) rect))) start
      unfold SpecTec.«$subst_functype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_resulttype_unroll_total params rect start)
      apply SpecTecExecution.Eval.bind_success
        (subst_resulttype_unroll_total results rect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.functype.FuncT
          (unrollValtypes params rect) (unrollValtypes results rect))

theorem subst_functype_unroll_deterministic (ft : SpecTec.functype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.functype,
        SpecTec.SpecTecCall.«$subst_functype» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» ft⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollFunctype ft rect)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_functype_unroll_total ft rect start)

end properties.wasm_module_not_ok.Rejection
