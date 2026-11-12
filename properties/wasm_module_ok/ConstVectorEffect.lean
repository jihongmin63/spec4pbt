import properties.wasm_module_ok.ConstLiteralDispatch
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstVectorEffect

theorem vector_type_call (v : SpecTec.vec_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.vectype,
        SpecTec.Call.«$type_vecop» SpecTec.v128 v⟩)
      n (.success (.of SpecTec.vectype.V128T)) n := by
  cases v with
  | V128 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_vecop_clauses» SpecTec.v128 (.V128 a)))
        n (.success (.of SpecTec.vectype.V128T)) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vecop:clause:0» SpecTec.v128 (.V128 a))
        n (.success (.of SpecTec.vectype.V128T)) n
      exact SpecTecExecution.Eval.pure _

theorem vec_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:84» c irt (.«VEC.CONST» v))
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [.VecT .V128T]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:84»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success (vector_type_call v n)
  exact SpecTecExecution.Eval.pure _

theorem vec_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:84» c irt (.«VEC.CONST» v))
      n (.success (.of iit)) fin) :
    iit =
      (⟨{ INS := (.NoEllipses, []),
           OUTS := (.NoEllipses, [.VecT .V128T]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
    fin = n := by
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (vec_clause_total c irt v n)
  cases hout
  exact ⟨rfl, hsupply⟩

end properties.wasm_module_ok.ConstVectorEffect
