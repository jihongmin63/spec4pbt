import properties.wasm_module_ok.ConstRefNullDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefNullCandidate

theorem ref_null_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (ht : SpecTec.heaptype) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«REF.NULL» ht)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨hheap, heffect, _⟩ :=
    (ConstRefNullDispatch.ref_null_dispatch_iff
      c irt ht iit start fin).1 h
  have hvalid : ValtypeValidation.valtypeValid c
      (.RefT (.«% %» .Null ht)) = true := hheap
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.RefT (.«% %» .Null ht)) hvalid
  refine ⟨[], [.RefT (.«% %» .Null ht)], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstRefNullCandidate
