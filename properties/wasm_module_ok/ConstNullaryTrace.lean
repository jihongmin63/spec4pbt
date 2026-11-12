import properties.wasm_module_ok.ConstBasicOrigin
import properties.wasm_module_ok.InstrsValidation
import properties.wasm_module_ok.LocalInitValidation
import properties.wasm_module_ok.PopBaseValidation
import properties.wasm_module_ok.PushValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstNullaryTrace

/-- A nullary singleton instruction can be run from the empty stack, with
the translated initialization, pop, push, and list order left intact. -/
theorem empty_one_effect_instrs_singleton
    (c : SpecTec.context) (u : SpecTec.valtype)
    (i : SpecTec.instr) (n : Nat)
    (h : ConstBasicOrigin.EmptyOneEffect c
      (SpecTec.ellipses.NoEllipses, []) u n i) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c
          (SpecTec.ellipses.NoEllipses, []) [i]⟩)
      n (.success (.of
        ((SpecTec.ellipses.NoEllipses, [u]),
          ([] : List SpecTec.idx)))) n := by
  obtain ⟨_, hinstr⟩ := h
  apply (InstrsValidation.instrs_cons_success_iff
    c (SpecTec.ellipses.NoEllipses, []) i []
    ((SpecTec.ellipses.NoEllipses, [u]),
      ([] : List SpecTec.idx)) n n).2
  refine ⟨(⟨{ INS := (SpecTec.ellipses.NoEllipses, []),
                 OUTS := (SpecTec.ellipses.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype),
    c, (SpecTec.ellipses.NoEllipses, []),
    (SpecTec.ellipses.NoEllipses, [u]),
    n, n, n, n, hinstr,
    LocalInitValidation.init_locals_nil_total c n,
    PopBaseValidation.pop_empty_total c n, ?_,
    InstrsValidation.instrs_nil_total c
      (SpecTec.ellipses.NoEllipses, [u]) n⟩
  simpa [PushValidation.pushOutcome, PushValidation.pushResult] using
    (PushValidation.push_total c
      (SpecTec.ellipses.NoEllipses, [u])
      (SpecTec.ellipses.NoEllipses, []) n)

/-- Every basic finite seed has a one-instruction translated trace from the
empty stack. The syntax permission is retained for `Const_ok` composition. -/
theorem basic_base_instrs_singleton
    (c : SpecTec.context) (u : SpecTec.valtype)
    (n : Nat) (hu : u ∈ ConstBasicSeed.basicBase c) :
    ∃ i : SpecTec.instr,
      ConstSyntaxDecision.syntaxAllowed c i = true ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c
            (SpecTec.ellipses.NoEllipses, []) [i]⟩)
        n (.success (.of
          ((SpecTec.ellipses.NoEllipses, [u]),
            ([] : List SpecTec.idx)))) n := by
  have horigin :=
    (ConstBasicOrigin.basic_base_iff_origin c
      (SpecTec.ellipses.NoEllipses, []) u n).1 hu
  have hmake (i : SpecTec.instr)
      (h : ConstBasicOrigin.EmptyOneEffect c
        (SpecTec.ellipses.NoEllipses, []) u n i) :
      ∃ i : SpecTec.instr,
        ConstSyntaxDecision.syntaxAllowed c i = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
            SpecTec.Call.Instrs_ok c
              (SpecTec.ellipses.NoEllipses, []) [i]⟩)
          n (.success (.of
            ((SpecTec.ellipses.NoEllipses, [u]),
              ([] : List SpecTec.idx)))) n :=
    ⟨i, h.1, empty_one_effect_instrs_singleton c u i n h⟩
  rcases horigin with ((((⟨v, hv⟩ | ⟨v, hv⟩) |
      ⟨ht, _, hv⟩) | ⟨x, dt, _, _, hv⟩) |
      ⟨x, t, _, _, hv⟩)
  · exact hmake (.CONST v) hv
  · exact hmake (.«VEC.CONST» v) hv
  · exact hmake (.«REF.NULL» ht) hv
  · exact hmake (.«REF.FUNC» x) hv
  · exact hmake (.«GLOBAL.GET» x) hv

end properties.wasm_module_ok.ConstNullaryTrace
