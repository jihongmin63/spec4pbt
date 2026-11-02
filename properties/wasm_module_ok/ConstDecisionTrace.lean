import properties.wasm_module_ok.ConstSyntaxDecision
import properties.wasm_module_ok.ConstExactSyntaxBoundary

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstDecisionTrace

theorem const_ok_decision_trace_iff
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      n (.success (.of ())) fin ↔
    (∀ i ∈ xs, ConstSyntaxDecision.syntaxAllowed c i = true) ∧
    ∃ (irt : SpecTec.inferresulttype) (indices : List SpecTec.idx)
      (ellipses : SpecTec.ellipses) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.SpecTecCall.Instrs_ok c
            (.NoEllipses, []) xs⟩)
        n (.success (.of (irt, indices))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [t]) irt⟩)
        middle (.success (.of (ellipses, ([] : List SpecTec.valtype))))
          fin := by
  rw [ConstExactSyntaxBoundary.const_ok_trace_iff]
  constructor
  · rintro ⟨hall, htrace⟩
    exact ⟨fun i hi =>
      (ConstSyntaxDecision.syntaxAllowed_iff c i).2 (hall i hi), htrace⟩
  · rintro ⟨hall, htrace⟩
    exact ⟨fun i hi =>
      (ConstSyntaxDecision.syntaxAllowed_iff c i).1 (hall i hi), htrace⟩

end properties.wasm_module_ok.ConstDecisionTrace
