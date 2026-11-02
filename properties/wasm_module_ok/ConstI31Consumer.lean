import properties.wasm_module_ok.ConstNumericConsumer
import properties.wasm_module_ok.ConstI31Dispatch
import properties.wasm_module_ok.ReadyHeapMatchBase
import properties.wasm_module_ok.ConstSingletonFinalPop

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstI31Consumer

theorem append_i31
    {origin current : SpecTec.context}
    {initial : SpecTec.inferresulttype}
    {xs : List SpecTec.instr}
    {start n : Nat}
    (stack : List SpecTec.valtype)
    (htrace : ConstConstructiveTrace.Trace origin initial xs current
      (.NoEllipses, stack ++ [.NumT .I32T]) start n) :
    ConstConstructiveTrace.Trace origin initial
      (xs ++ [.«REF.I31»]) current
      (.NoEllipses, stack ++
        [.RefT (.«% %» .NoNull .I31HT)]) start n := by
  have hinstr := ConstI31Dispatch.i31_dispatch_total current
    (.NoEllipses, stack ++ [.NumT .I32T]) n
  have hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        ((stack ++ ([.NumT .I32T] : List SpecTec.valtype)).drop
          ((stack ++ ([.NumT .I32T] : List SpecTec.valtype)).length - 1))
        [.NumT .I32T]⟩)
      n (.success (.of ())) n := by
    simpa using ConstNumericConsumer.match_numeric_singleton
      current .I32T n
  have hconsumer := ConstConsumerTrace.trace_snoc_of_match
    (stack ++ [.NumT .I32T]) [.NumT .I32T]
    (.RefT (.«% %» .NoNull .I31HT)) .«REF.I31»
    htrace hinstr (by simp) hmatch
  simpa only [List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.add_sub_cancel_right,
    List.take_append, List.take_of_length_le,
    Nat.sub_self, List.take_zero, List.take_length,
    List.nil_append, List.append_assoc] using hconsumer

theorem i31_syntax_allowed (c : SpecTec.context) :
    ConstSyntaxDecision.syntaxAllowed c .«REF.I31» = true := by
  exact (ConstSyntaxDecision.syntaxAllowed_iff c .«REF.I31»).2
    .refI31

theorem i31_heap_self_match (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        c.TYPES .I31HT .I31HT⟩)
      n (.success (.of true)) n := by
  simpa [ReadyHeapMatchBase.baseMatch,
    ReadyHeapMatchBase.baseMatchFuel,
    ReadyHeapMatchSimpleBase.simpleBaseMatch] using
    (ReadyHeapMatchBase.baseMatch_eval c.TYPES .I31HT .I31HT n
      (by simp [HeaptypeValidation.baseHeaptypes])
      (by simp [HeaptypeValidation.baseHeaptypes]))

theorem i31_value_self_match (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype»
        c.TYPES
        (.RefT (.«% %» .NoNull .I31HT))
        (.RefT (.«% %» .NoNull .I31HT))⟩)
      n (.success (.of true)) n := by
  simpa [MatchReftypeConditional.matchReftypeResult,
    MatchNullValidation.matchNullResult] using
    (MatchValtypeLocal.match_valtype_ref_ref_pair_total
      c.TYPES (fun _ _ => true)
      (.«% %» .NoNull .I31HT)
      (.«% %» .NoNull .I31HT) n
      (by simpa [MatchValtypeLocal.refHeap] using
        i31_heap_self_match c n))

theorem i31_result_self_match (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c
        [.RefT (.«% %» .NoNull .I31HT)]
        [.RefT (.«% %» .NoNull .I31HT)]⟩)
      n (.success (.of ())) n := by
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c [.RefT (.«% %» .NoNull .I31HT)]
      [.RefT (.«% %» .NoNull .I31HT)] n n).2
  refine ⟨rfl, ?_⟩
  exact (MatchResulttypeValidation.match_iter_cons_success_iff
    c (.RefT (.«% %» .NoNull .I31HT))
      (.RefT (.«% %» .NoNull .I31HT)) [] [] n n).2
      ⟨n, i31_value_self_match c n,
        MatchResulttypeValidation.match_iter_nil_total c n⟩

theorem i31_const_expression (c : SpecTec.context) (n : Nat) :
    ∃ xs : List SpecTec.instr,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c
          (.RefT (.«% %» .NoNull .I31HT)) xs⟩)
        n (.success (.of ())) n := by
  have hbase : SpecTec.valtype.NumT .I32T ∈
      ConstBasicSeed.basicBase c := by
    exact (ConstBasicSeed.basic_base_mem_iff c _).2
      (by simp [ConstBasicSeed.basicSeed,
        ConstLiteralProduction.literalSeed,
        ConstNumericProduction.numericSeed])
  obtain ⟨xs, hsyntax, htrace⟩ :=
    ConstBasicTrace.basic_list_trace c c
      (ConstStaticAgreement.refl c) [.NumT .I32T]
      (by
        intro u hu
        have heq : u = SpecTec.valtype.NumT .I32T := by
          simpa using hu
        subst u
        exact hbase)
      [] n
  have hi31 := append_i31 [] (by simpa using htrace)
  have hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)])
          (.NoEllipses, [.RefT (.«% %» .NoNull .I31HT)])⟩)
      n (.success (.of (SpecTec.ellipses.NoEllipses,
        ([] : List SpecTec.valtype)))) n :=
    ConstSingletonFinalPop.singleton_final_pop_of_match_resulttype
      c (.RefT (.«% %» .NoNull .I31HT))
        (.RefT (.«% %» .NoNull .I31HT)) n
      (i31_result_self_match c n)
  refine ⟨xs ++ [.«REF.I31»],
    (ConstDecisionTrace.const_ok_decision_trace_iff
      c (.RefT (.«% %» .NoNull .I31HT))
        (xs ++ [.«REF.I31»]) n n).2 ?_⟩
  refine ⟨?_, (.NoEllipses,
    [.RefT (.«% %» .NoNull .I31HT)]),
    ([] : List SpecTec.idx), .NoEllipses, n, ?_, hpop⟩
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact hsyntax i hi
    · exact i31_syntax_allowed c
  · exact ConstConstructiveTrace.trace_to_instrs
      (by simpa using hi31)

end properties.wasm_module_ok.ConstI31Consumer
