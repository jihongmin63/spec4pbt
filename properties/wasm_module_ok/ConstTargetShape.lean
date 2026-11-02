import properties.wasm_module_ok.MatchValtypeShape

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTargetShape

theorem bot_candidate_after_adding_global
    (c : SpecTec.context) :
    SpecTec.valtype.BotT ∈
      FiniteValidTypes.candidateUniverse
        { c with GLOBALS := [.GlobalT .Cons .BotT] } := by
  exact FiniteValidTypes.global_output_mem_candidateUniverse
    { c with GLOBALS := [.GlobalT .Cons .BotT] }
    0 .Cons .BotT (by simp)

theorem const_ok_target_outer_shape
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (start fin : Nat)
    (hnoBot : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) fin) :
    (∃ a : SpecTec.numtype, t = .NumT a) ∨
      (∃ a : SpecTec.vectype, t = .VecT a) ∨
      (∃ a : SpecTec.reftype, t = .RefT a) := by
  obtain ⟨u, hu, before, after, hmatch⟩ :=
    ConstTargetCandidate.const_ok_target_has_candidate_match
      c t xs start fin h
  rcases MatchValtypeShape.match_valtype_true_shape
      c u t before after hmatch with
    hbot | ⟨a, b, _, ht⟩ | ⟨a, b, _, ht⟩ | ⟨a, b, _, ht⟩
  · exact False.elim (hnoBot (hbot ▸ hu))
  · exact Or.inl ⟨b, ht⟩
  · exact Or.inr (Or.inl ⟨b, ht⟩)
  · exact Or.inr (Or.inr ⟨b, ht⟩)

end properties.wasm_module_ok.ConstTargetShape
