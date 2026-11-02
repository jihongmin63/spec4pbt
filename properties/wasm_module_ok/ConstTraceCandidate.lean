import properties.wasm_module_ok.ConstInstrsClosure
import properties.wasm_module_ok.ConstExactSyntaxBoundary

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTraceCandidate

theorem const_ok_trace_candidates
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) fin) :
    ∃ (irt : SpecTec.inferresulttype) (indices : List SpecTec.idx)
      (ellipses : SpecTec.ellipses) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.SpecTecCall.Instrs_ok c
            (.NoEllipses, []) xs⟩)
        start (.success (.of (irt, indices))) middle ∧
      irt.1 = .NoEllipses ∧
      (∀ u ∈ irt.2, u ∈ FiniteValidTypes.candidateUniverse c) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [t]) irt⟩)
        middle (.success (.of (ellipses, ([] : List SpecTec.valtype))))
          fin := by
  obtain ⟨hsyntax, irt, indices, ellipses, middle, hinstr, hpop⟩ :=
    (ConstExactSyntaxBoundary.const_ok_trace_iff
      c t xs start fin).1 h
  have hnil : ∀ u ∈ ([] : List SpecTec.valtype),
      u ∈ FiniteValidTypes.candidateUniverse c := by
    simp
  obtain ⟨hno, hclosed⟩ :=
    ConstInstrsClosure.instrs_syntax_entries_closed
      c c xs [] (irt, indices) start middle
      hsyntax rfl hinstr hnil
  exact ⟨irt, indices, ellipses, middle,
    hinstr, hno, hclosed, hpop⟩

end properties.wasm_module_ok.ConstTraceCandidate
