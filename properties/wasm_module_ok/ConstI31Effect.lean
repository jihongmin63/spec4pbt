import properties.wasm_module_ok.ConstVectorDispatch
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstI31Effect

theorem i31_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:57» c irt .«REF.I31»)
      n (.success (.of
        (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
             OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:57»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure _

theorem i31_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:57» c irt .«REF.I31»)
      n (.success (.of iit)) fin) :
    iit =
      (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
           OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
    fin = n := by
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h (i31_clause_total c irt n)
  cases hout
  exact ⟨rfl, hsupply⟩

end properties.wasm_module_ok.ConstI31Effect
