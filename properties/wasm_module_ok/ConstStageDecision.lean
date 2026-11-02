import properties.wasm_module_ok.ConstStageEntry
import properties.wasm_module_ok.ConstExpressionDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStageDecision

/-- The backward initializer entry condition is exactly nonemptiness of the
executable expression decision on a validated module context. -/
theorem has_const_continuation_iff_expression_result
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    ConstStageEntry.HasConstContinuation c t ↔
      ∃ xs : SpecTec.const,
        ConstExpressionDecision.constantExpressionResult c t xs = true := by
  have hready := CandidateTraceReady.trace_ready_at m tr c hc
  have hprov := CandidateTraceReady.trace_provenance_at m tr c hc
  have hnested := ConstTraceNestedReady.trace_nested_ready_at m tr c hc
  constructor
  · intro hentry
    obtain ⟨xs, n, hconst⟩ :=
      (ConstProductiveDecision.productive_fillable_iff_const_ok
        m tr c hc t htarget htable).1 hentry
    exact ⟨xs,
      (ConstExpressionDecision.constant_expression_result_iff_const_ok
        c t xs n hready hprov hnested htable).2 hconst⟩
  · rintro ⟨xs, hresult⟩
    have hconst :=
      (ConstExpressionDecision.constant_expression_result_iff_const_ok
        c t xs 0 hready hprov hnested htable).1 hresult
    exact ConstFillabilityDecision.const_ok_implies_fillable
      m tr c hc t xs 0 0 hconst htarget htable

theorem globaltype_continuation_iff_expression_result
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (mutation : SpecTec.«mut») (t : SpecTec.valtype)
    (typeStart typeFinish : Nat)
    (htype : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Globaltype_ok c (.GlobalT mutation t)⟩)
      typeStart (.success (.of ())) typeFinish) :
    ConstStageEntry.HasConstContinuation c t ↔
      ∃ xs : SpecTec.const,
        ConstExpressionDecision.constantExpressionResult c t xs = true := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.globaltype_target_in_extended_and_table
      c mutation t typeStart typeFinish htype
  exact has_const_continuation_iff_expression_result
    m tr c hc t htarget htable

theorem tabletype_continuation_iff_expression_result
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (addr : SpecTec.addrtype) (lim : SpecTec.limits)
    (rt : SpecTec.reftype)
    (typeStart typeFinish : Nat)
    (htype : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Tabletype_ok c (.TableT addr lim rt)⟩)
      typeStart (.success (.of ())) typeFinish) :
    ConstStageEntry.HasConstContinuation c (.RefT rt) ↔
      ∃ xs : SpecTec.const,
        ConstExpressionDecision.constantExpressionResult c (.RefT rt) xs = true := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.tabletype_target_in_extended_and_table
      c addr lim rt typeStart typeFinish htype
  exact has_const_continuation_iff_expression_result
    m tr c hc (.RefT rt) htarget htable

theorem elem_continuation_iff_expression_result
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (result : SpecTec.context) (e : SpecTec.elem)
    (elemStart elemFinish : Nat)
    (helem : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elem_ok c e⟩)
      elemStart (.success (.of result)) elemFinish) :
    ConstStageEntry.HasConstContinuation c (.RefT e.ETYPE) ↔
      ∃ xs : SpecTec.const,
        ConstExpressionDecision.constantExpressionResult c
          (.RefT e.ETYPE) xs = true := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.elem_target_in_extended_and_table
      c result e elemStart elemFinish helem
  exact has_const_continuation_iff_expression_result
    m tr c hc (.RefT e.ETYPE) htarget htable

end properties.wasm_module_ok.ConstStageDecision
