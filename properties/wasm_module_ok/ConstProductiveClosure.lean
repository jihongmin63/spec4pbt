import properties.wasm_module_ok.ConstMatchAwareClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstProductiveClosure

/-- Actual output constructors, without the operand-saturation set itself. -/
def coveredOutputs (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  ConstBasicSeed.basicBase c ∪
    ConstStructImplicitProduction.structImplicitBase c ∪
    ConstArrayFixedZeroProduction.arrayFixedZeroBase c ∪
    ConstI31Production.i31Outputs c s ∪
    ConstStructExplicitProduction.structExplicitOutputs c s ∪
    ConstExternConvertProduction.externTypeOutputs c s

theorem covered_outputs_mem_iff (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    u ∈ coveredOutputs c s ↔ ConstOutputCoverage.Covered c s u := by
  simp only [coveredOutputs, Finset.mem_union,
    ConstI31Production.i31_outputs_mem_iff,
    ConstStructExplicitProduction.struct_explicit_outputs_mem_iff,
    ConstExternConvertProduction.extern_type_outputs_mem_iff]
  constructor
  · rintro (((((hbasic | himplicit) | harray) | hi31) | hstruct) | hextern)
    · exact .basic hbasic
    · exact .structImplicit himplicit
    · exact .array harray
    · exact .i31 hi31
    · exact .structExplicit hstruct
    · exact .externConvert hextern
  · intro h
    cases h with
    | basic h => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    | structImplicit h => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    | array h => exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    | i31 h => exact Or.inl (Or.inl (Or.inr h))
    | structExplicit h => exact Or.inl (Or.inr h)
    | externConvert h => exact Or.inr h

/-- Finite forward production, retaining old outputs but never promoting a
match-only operand type to a produced output. -/
def productiveStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  s ∪ coveredOutputs c
    (ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c s))

theorem productive_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    productiveStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hs | hp
  · exact hsub hs
  · exact ConstCoveredCandidate.covered_output_candidate c _ u
      ((covered_outputs_mem_iff c _ u).1 hp)

theorem productive_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ productiveStep c s := by
  intro u hu
  exact Finset.mem_union_left _ hu

theorem covered_outputs_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    coveredOutputs c s ⊆ coveredOutputs c t := by
  intro u hu
  apply (covered_outputs_mem_iff c t u).2
  cases (covered_outputs_mem_iff c s u).1 hu with
  | basic h => exact .basic h
  | structImplicit h => exact .structImplicit h
  | array h => exact .array h
  | i31 h =>
    exact .i31 (ConstI31Production.i31_step_mono s t u hsub h)
  | structExplicit h =>
    exact .structExplicit
      (ConstStructExplicitProduction.struct_explicit_step_mono
        c s t u hsub h)
  | externConvert h =>
    exact .externConvert
      (ConstExternConvertProduction.extern_type_step_mono s t u hsub h)

theorem productive_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    productiveStep c s ⊆ productiveStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hs | houtput
  · exact Finset.mem_union_left _ (hsub hs)
  · apply Finset.mem_union_right
    apply covered_outputs_mono c _ _
      (ConstExtendedMatchSaturation.extended_match_saturation_mono
        c _ _ (ConstMatchAwareClosure.sources_of_mono c s t hsub))
    exact houtput

theorem productive_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (productiveStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (productiveStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (productiveStep c)
    (productive_step_bounded c)
    (fun s _ => productive_step_inflate c s)

/-- Every successful constant instruction with a successful pop contributes
its actual output to the productive step. -/
theorem output_mem_productive_step
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start middle instructionFinish popStart popFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of result)) popFinish)
    (hbounded : s ⊆ FiniteValidTypes.candidateUniverse c)
    (havailable : ∀ actual ∈ available, actual ∈ s)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ productiveStep c s := by
  let sources := ConstMatchAwareClosure.sourcesOf c s
  have hsource : ∀ actual ∈ available, actual ∈ sources := by
    intro actual hmem
    exact (ConstMatchAwareClosure.sources_of_mem_iff c s actual hbounded).2
      (havailable actual hmem)
  have hinputs :=
    ConstExtendedMatchSaturation.const_pop_inputs_in_extended_saturation
      c irt i iit available sources result
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hready hsource hactual hrequired
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  have hcovered := ConstOutputCoverage.covered_of_syntax
    c irt (ConstExtendedMatchSaturation.extendedMatchSaturation c sources)
    i iit u middle instructionFinish hsyntax hcall hinputs houts
  exact Finset.mem_union_right _
    ((covered_outputs_mem_iff c _ u).2 hcovered)

theorem productive_step_no_bot (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    SpecTec.valtype.BotT ∉ productiveStep c s := by
  intro hbot
  exact hno (productive_step_bounded c s hsub hbot)

theorem productive_iterate_no_bot (c : SpecTec.context)
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (round : Nat) :
    SpecTec.valtype.BotT ∉
      FiniteClosure.iterate (productiveStep c) round := by
  intro hbot
  exact hno (FiniteClosure.iterate_bounded
    (FiniteValidTypes.candidateUniverse c) (productiveStep c)
    (productive_step_bounded c) round hbot)

end properties.wasm_module_ok.ConstProductiveClosure
