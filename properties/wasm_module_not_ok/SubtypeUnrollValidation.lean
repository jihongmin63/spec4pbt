import properties.wasm_module_not_ok.HeaptypeListUnrollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollSubtype (st : SpecTec.subtype) (rect : SpecTec.rectype) : SpecTec.subtype :=
  match st with
  | .SubT fin hts strt =>
      .SubT fin (unrollHeaptypes hts rect) (unrollStrtype strt rect)

theorem subst_subtype_unroll_total (st : SpecTec.subtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» st⟩)
      start (.success (.of (unrollSubtype st rect))) start := by
  cases st with
  | SubT fin hts strt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_subtype_clauses» SpecTec.rectype rect
            SpecTec.SpecTecCall.«$s_unroll» (.SubT fin hts strt)) ())
        start (.success (.of (unrollSubtype (.SubT fin hts strt) rect))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_subtype:clause:0» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» (.SubT fin hts strt))
        start (.success (.of (unrollSubtype (.SubT fin hts strt) rect))) start
      unfold SpecTec.«$subst_subtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_heaptype_list_unroll_total hts rect start)
      apply SpecTecExecution.Eval.bind_success
        (subst_strtype_unroll_total strt rect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.subtype.SubT fin
          (unrollHeaptypes hts rect) (unrollStrtype strt rect))

theorem subst_subtype_unroll_deterministic (st : SpecTec.subtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype» SpecTec.rectype rect
          SpecTec.SpecTecCall.«$s_unroll» st⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollSubtype st rect)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_subtype_unroll_total st rect start)

end properties.wasm_module_not_ok.Rejection
