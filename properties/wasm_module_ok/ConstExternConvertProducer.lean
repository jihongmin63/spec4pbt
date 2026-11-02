import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstConstructiveMatchStatic
import properties.wasm_module_ok.ConstConsumerTrace
import properties.wasm_module_ok.ConstExternConvertProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternConvertProducer

private theorem extern_input_self_match
    (c : SpecTec.context) (nu : SpecTec.null)
    (op : SpecTec.externop_) :
    CandidateValMatch.candidateValMatch c
      (ConstExternConvertProduction.externInput nu op)
      (ConstExternConvertProduction.externInput nu op) = true := by
  cases nu <;> cases op <;>
    simp [CandidateValMatch.candidateValMatch,
      ConstExternConvertProduction.externInput,
      ExternopTypeDecision.typeExternopResult,
      MatchValtypeConditional.matchValtypeResult,
      MatchReftypeConditional.matchReftypeResult,
      ReadyHeapMatch.readyHeapMatch,
      ReadyHeapMatchBase.baseMatch,
      ReadyHeapMatchBase.baseMatchFuel,
      ReadyHeapMatchSimpleBase.simpleBaseMatch,
      MatchNullValidation.matchNullResult,
      HeaptypeValidation.baseHeaptypes]

theorem nullable_extern_output_basic
    (c : SpecTec.context) (op : SpecTec.externop_) :
    ConstExternConvertProduction.externOutput .Null op ∈
      ConstBasicSeed.basicBase c := by
  have hnull : ConstExternConvertProduction.externOutput .Null op ∈
      ConstRefNullProduction.refNullBase c :=
    (ConstRefNullProduction.ref_null_base_mem_iff c _).2 (by
      cases op <;>
        rfl)
  simp only [ConstBasicSeed.basicBase, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hnull))

theorem nullable_extern_output_produces
    (c : SpecTec.context) (op : SpecTec.externop_) :
    ConstConstructiveProducer.Produces c
      (ConstExternConvertProduction.externOutput .Null op) :=
  ConstConstructiveProducer.basic_produces c _
    (nullable_extern_output_basic c op)

theorem nonnull_match_source_ref
    (c : SpecTec.context) (a : SpecTec.valtype)
    (op : SpecTec.externop_)
    (hnotbot : a ≠ .BotT)
    (hmatch : CandidateValMatch.candidateValMatch c a
      (ConstExternConvertProduction.externInput .NoNull op) = true) :
    ∃ ht, a = .RefT (.«% %» .NoNull ht) := by
  cases a with
  | NumT nt =>
    cases op <;>
      simp [CandidateValMatch.candidateValMatch,
        ConstExternConvertProduction.externInput,
        ExternopTypeDecision.typeExternopResult,
        MatchValtypeConditional.matchValtypeResult] at hmatch
  | VecT vt =>
    cases op <;>
      simp [CandidateValMatch.candidateValMatch,
        ConstExternConvertProduction.externInput,
        ExternopTypeDecision.typeExternopResult,
        MatchValtypeConditional.matchValtypeResult] at hmatch
  | BotT => exact False.elim (hnotbot rfl)
  | RefT rt =>
    cases rt with
    | «% %» nu ht =>
      cases nu with
      | NoNull => exact ⟨ht, rfl⟩
      | Null =>
        cases op <;>
          simp [CandidateValMatch.candidateValMatch,
            ConstExternConvertProduction.externInput,
            ExternopTypeDecision.typeExternopResult,
            MatchValtypeConditional.matchValtypeResult,
            MatchReftypeConditional.matchReftypeResult,
            MatchNullValidation.matchNullResult] at hmatch

theorem nonnull_extern_produces_of_match
    (origin : SpecTec.context) (a : SpecTec.valtype)
    (ht : SpecTec.heaptype) (op : SpecTec.externop_)
    (ha : a = .RefT (.«% %» .NoNull ht))
    (hmatch : CandidateValMatch.candidateValMatch origin a
      (ConstExternConvertProduction.externInput .NoNull op) = true)
    (hproduce : ConstConstructiveProducer.Produces origin a)
    (hready : CandidateTypeReady.Ready origin)
    (hactualTable : CandidateValMatch.InTableVal origin a)
    (hrequiredTable : CandidateValMatch.InTableVal origin
      (ConstExternConvertProduction.externInput .NoNull op)) :
    ConstConstructiveProducer.Produces origin
      (ConstExternConvertProduction.externOutput .NoNull op) := by
  let required := ConstExternConvertProduction.externInput .NoNull op
  let target := ConstExternConvertProduction.externOutput .NoNull op
  intro current hstatic stack n
  obtain ⟨xs, next, hsyntax, htrace, hnext⟩ :=
    hproduce current hstatic stack n
  have hpairs : List.Forall₂
      (fun x y => CandidateValMatch.candidateValMatch origin x y = true)
      [a] [required] := by
    exact List.Forall₂.cons hmatch List.Forall₂.nil
  have hmatchCall :=
    ConstConstructiveMatchStatic.match_resulttype_at_static_context
      origin next [a] [required] n hnext hready hpairs
      (by
        intro x hx
        have heq : x = a := by simpa using hx
        subst x
        exact hactualTable)
      (by
        intro x hx
        have heq : x = required := by simpa using hx
        subst x
        exact hrequiredTable)
  have hpeek : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 (.NoEllipses, stack ++ [a])) =
      some (.«% %» .NoNull ht) := by
    simp [PeekDecision.peekResult, PeekRefDecision.peekRefResult, ha]
  have hinstr :=
    (ConstExternConvertDecision.extern_convert_success_iff_result
      next (.NoEllipses, stack ++ [a]) op
      (ConstExternConvertProduction.externInstrType .NoNull op) n n).2
      ⟨ConstExternConvertProduction.extern_convert_result_of_peek
        (.NoEllipses, stack ++ [a]) .NoNull ht op hpeek, rfl⟩
  have htraceNew := ConstConsumerTrace.trace_snoc_after_operands
    stack [a] [required] target (.«EXTERN.CONVERT» op)
    htrace (by simpa [ConstExternConvertProduction.externInstrType,
      required, target] using hinstr) (by simp) hmatchCall
  refine ⟨xs ++ [.«EXTERN.CONVERT» op], next, ?_, htraceNew, hnext⟩
  intro i hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact hsyntax i hi
  · simp [ConstSyntaxDecision.syntaxAllowed,
      ConstArithmeticValidation.arithmeticOps]

theorem extern_type_step_produces
    (origin : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype)
    (hstep : ConstExternConvertProduction.externTypeStep s u = true)
    (hsound : ∀ v ∈ s, ConstConstructiveProducer.Produces origin v)
    (hready : CandidateTypeReady.Ready origin)
    (hsourceTable : ∀ v ∈ s, CandidateValMatch.InTableVal origin v) :
    ConstConstructiveProducer.Produces origin u := by
  obtain ⟨nu, op, hinput, rfl⟩ :=
    (ConstExternConvertProduction.extern_type_step_iff s u).1 hstep
  let source := ConstExternConvertProduction.externInput nu op
  let target := ConstExternConvertProduction.externOutput nu op
  intro current hstatic stack n
  obtain ⟨xs, next, hsyntax, htrace, hnext⟩ :=
    (hsound source hinput) current hstatic stack n
  have hpairs : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch origin a r = true)
      [source] [source] := by
    exact List.Forall₂.cons (extern_input_self_match origin nu op)
      List.Forall₂.nil
  have hmatch :=
    ConstConstructiveMatchStatic.match_resulttype_at_static_context
      origin next [source] [source] n hnext hready hpairs
      (by
        intro a ha
        have heq : a = source := by simpa using ha
        subst a
        exact hsourceTable source hinput)
      (by
        intro a ha
        have heq : a = source := by simpa using ha
        subst a
        exact hsourceTable source hinput)
  have hpeek : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 (.NoEllipses, stack ++ [source])) =
      some (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1) := by
    simp [PeekDecision.peekResult, PeekRefDecision.peekRefResult,
      source, ConstExternConvertProduction.externInput]
  have hinstr :=
    (ConstExternConvertDecision.extern_convert_success_iff_result
      next (.NoEllipses, stack ++ [source]) op
      (ConstExternConvertProduction.externInstrType nu op) n n).2
      ⟨ConstExternConvertProduction.extern_convert_result_of_peek
        (.NoEllipses, stack ++ [source]) nu
        (ExternopTypeDecision.typeExternopResult op).1 op hpeek, rfl⟩
  have htraceNew := ConstConsumerTrace.trace_snoc_after_operands
    stack [source] [source] target (.«EXTERN.CONVERT» op)
    htrace (by simpa [ConstExternConvertProduction.externInstrType,
      source, target] using hinstr) (by simp) hmatch
  refine ⟨xs ++ [.«EXTERN.CONVERT» op], next, ?_, htraceNew, hnext⟩
  intro i hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact hsyntax i hi
  · simp [ConstSyntaxDecision.syntaxAllowed,
      ConstArithmeticValidation.arithmeticOps]

theorem extern_saturated_step_produces
    (origin : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse origin)
    (hno : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse origin)
    (hready : CandidateTypeReady.Ready origin)
    (hprov : CandidateUniverseReady.Provenance origin)
    (hnested : CandidateNestedReady.nestedTableReady origin = true)
    (hsound : ∀ a ∈ s, ConstConstructiveProducer.Produces origin a)
    (hstep : ConstExternConvertProduction.externTypeStep
      (ConstExtendedMatchSaturation.extendedMatchSaturation origin
        (ConstMatchAwareClosure.sourcesOf origin s)) u = true) :
    ConstConstructiveProducer.Produces origin u := by
  obtain ⟨nu, op, hrequired, rfl⟩ :=
    (ConstExternConvertProduction.extern_type_step_iff _ u).1 hstep
  cases nu with
  | Null => exact nullable_extern_output_produces origin op
  | NoNull =>
    let required := ConstExternConvertProduction.externInput .NoNull op
    obtain ⟨hcandidate, a, hasource, hmatch⟩ :=
      (ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
        origin (ConstMatchAwareClosure.sourcesOf origin s) required).1
        hrequired
    have ha : a ∈ s :=
      (ConstMatchAwareClosure.sources_of_mem_iff origin s a hsub).1
        hasource
    have hnotbot : a ≠ .BotT := by
      intro heq
      subst a
      exact hno (hsub ha)
    obtain ⟨ht, hshape⟩ :=
      nonnull_match_source_ref origin a op hnotbot hmatch
    exact nonnull_extern_produces_of_match origin a ht op hshape
      hmatch (hsound a ha) hready
      (CandidateUniverseReady.candidate_universe_in_table
        origin a hprov (hsub ha))
      (ConstExtendedCandidateReady.extended_candidate_in_table
        origin hprov hnested required hcandidate)

end properties.wasm_module_ok.ConstExternConvertProducer
