import properties.wasm_module_ok.InstrsCandidateClosure
import properties.wasm_module_ok.ConstSyntaxCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstInstrsClosure

theorem instrs_syntax_entries_closed
    (base c : SpecTec.context) (xs : List SpecTec.instr)
    (stack : List SpecTec.valtype)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start fin : Nat)
    (hsyntax : ∀ i ∈ xs,
      ConstAdditionalSyntaxValidation.Syntax base i)
    (hc : FiniteValidTypes.candidateUniverse c =
      FiniteValidTypes.candidateUniverse base)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c (.NoEllipses, stack) xs⟩)
      start (.success (.of result)) fin)
    (hstack : ∀ t ∈ stack,
      t ∈ FiniteValidTypes.candidateUniverse base) :
    result.1.1 = .NoEllipses ∧
      ∀ t ∈ result.1.2,
        t ∈ FiniteValidTypes.candidateUniverse base := by
  refine InstrsCandidateClosure.instrs_candidate_entries_closed
    base xs ?_ c stack result start fin hc h hstack
  intro i hi current irt iit n finalSupply hcurrent hinstr
  obtain ⟨need, outs, hins, houts, hmembers⟩ :=
    ConstSyntaxCandidate.syntax_instruction_effect_candidate
      base current i irt iit n finalSupply
      (hsyntax i hi) hinstr
  refine ⟨need, outs, hins, houts, ?_⟩
  intro t ht
  rw [← hcurrent]
  exact hmembers t ht

end properties.wasm_module_ok.ConstInstrsClosure
