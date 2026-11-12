import properties.wasm_module_ok.ConstI31Dispatch
import properties.wasm_module_ok.HeaptypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefNullEffect

theorem ref_null_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (ht : SpecTec.heaptype) (n : Nat)
    (hvalid : HeaptypeValidation.heaptypeValid c ht = true) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:50» c irt (.«REF.NULL» ht))
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [.RefT (.«% %» .Null ht)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:50»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
    ((HeaptypeValidation.heaptype_success_iff_valid c ht n n).2 ⟨hvalid, rfl⟩)
  exact SpecTecExecution.Eval.pure _

theorem ref_null_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (ht : SpecTec.heaptype) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:50» c irt (.«REF.NULL» ht))
      n (.success (.of iit)) fin) :
    HeaptypeValidation.heaptypeValid c ht = true ∧
    iit =
      (⟨{ INS := (.NoEllipses, []),
           OUTS := (.NoEllipses, [.RefT (.«% %» .Null ht)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
    fin = n := by
  have hvalid : HeaptypeValidation.heaptypeValid c ht = true := by
    unfold SpecTec.«Instr_ok:clause:50» at h
    cases h with
    | bind_success _ htail =>
        cases htail with
        | bind_success hcall _ =>
            exact ((HeaptypeValidation.heaptype_success_iff_valid c ht _ _).1 hcall).1
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (ref_null_clause_total c irt ht n hvalid)
  cases hout
  exact ⟨hvalid, rfl, hsupply⟩

end properties.wasm_module_ok.ConstRefNullEffect
