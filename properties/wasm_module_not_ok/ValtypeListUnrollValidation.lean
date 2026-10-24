import properties.wasm_module_not_ok.ValtypeUnrollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollValtypes (ts : List SpecTec.valtype) (rect : SpecTec.rectype) :
    List SpecTec.valtype :=
  ts.map (fun t => unrollValtype t rect)

theorem subst_valtype_list_unroll_total (ts : List SpecTec.valtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_resulttype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» ts⟩)
      start (.success (.of (unrollValtypes ts rect))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» []) ())
        start (.success (.of (unrollValtypes [] rect))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
          SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» [])
        start (.success (.of (unrollValtypes [] rect))) start
      simpa [SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»,
        unrollValtypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.valtype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» (t :: ts)) ())
        start (.success (.of (unrollValtypes (t :: ts) rect))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
            SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
            SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» (t :: ts))
          start (.success (.of (unrollValtypes (t :: ts) rect))) start
        unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_valtype_unroll_total t rect start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [unrollValtypes] using
          (SpecTecExecution.Eval.pure
            (unrollValtype t rect :: unrollValtypes ts rect) (n := start))

theorem subst_valtype_list_unroll_deterministic (ts : List SpecTec.valtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_resulttype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.SpecTecCall.«$s_unroll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollValtypes ts rect)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_valtype_list_unroll_total ts rect start)

end properties.wasm_module_not_ok.Rejection
