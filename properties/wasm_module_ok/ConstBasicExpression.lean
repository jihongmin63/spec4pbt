import properties.wasm_module_ok.ConstNullaryTrace
import properties.wasm_module_ok.ConstSingletonFinalPop
import properties.wasm_module_ok.ConstDecisionTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicExpression

/-- Every basic seed matching the requested type has an actual one-instruction
constant expression. This constructs the final translated `$pop` as well. -/
theorem basic_base_const_ok_of_match
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hbase : u ∈ ConstBasicSeed.basicBase c)
    (hready : CandidateTypeReady.Ready c)
    (hu : CandidateValMatch.InTableVal c u)
    (ht : CandidateValMatch.InTableVal c t)
    (hmatch : CandidateValMatch.candidateValMatch c u t = true) :
    ∃ i : SpecTec.instr,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t [i]⟩)
        n (.success (.of ())) n := by
  obtain ⟨i, hsyntax, hlist⟩ :=
    ConstNullaryTrace.basic_base_instrs_singleton c u n hbase
  refine ⟨i, (ConstDecisionTrace.const_ok_decision_trace_iff
    c t [i] n n).2 ?_⟩
  refine ⟨?_, (SpecTec.ellipses.NoEllipses, [u]),
    ([] : List SpecTec.idx), SpecTec.ellipses.NoEllipses,
    n, hlist, ?_⟩
  · intro j hj
    have : j = i := by simpa using hj
    subst j
    exact hsyntax
  · exact ConstSingletonFinalPop.singleton_final_pop_of_candidate_match
      c u t n hready hu ht hmatch

end properties.wasm_module_ok.ConstBasicExpression
