import properties.wasm_module_ok.ConstValidatedTarget

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStageEntry

/-- Backward entry condition for choosing an initializer expression after its
target type and its validated module context have been fixed. -/
def HasConstContinuation (c : SpecTec.context) (t : SpecTec.valtype) : Prop :=
  ConstFillabilityDecision.constFillable c t = true

theorem has_const_continuation_iff
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    HasConstContinuation c t ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
          start (.success (.of ())) finish := by
  exact ConstFillabilityDecision.const_fillable_iff_const_ok
    m tr c hc t htarget htable

theorem globaltype_continuation_iff
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
    HasConstContinuation c t ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
          start (.success (.of ())) finish := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.globaltype_target_in_extended_and_table
      c mutation t typeStart typeFinish htype
  exact has_const_continuation_iff m tr c hc t htarget htable

theorem tabletype_continuation_iff
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
    HasConstContinuation c (.RefT rt) ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c (.RefT rt) xs⟩)
          start (.success (.of ())) finish := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.tabletype_target_in_extended_and_table
      c addr lim rt typeStart typeFinish htype
  exact has_const_continuation_iff m tr c hc (.RefT rt) htarget htable

theorem elem_continuation_iff
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (result : SpecTec.context) (e : SpecTec.elem)
    (elemStart elemFinish : Nat)
    (helem : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elem_ok c e⟩)
      elemStart (.success (.of result)) elemFinish) :
    HasConstContinuation c (.RefT e.ETYPE) ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c (.RefT e.ETYPE) xs⟩)
          start (.success (.of ())) finish := by
  obtain ⟨htarget, htable⟩ :=
    ConstValidatedTarget.elem_target_in_extended_and_table
      c result e elemStart elemFinish helem
  exact has_const_continuation_iff m tr c hc (.RefT e.ETYPE)
    htarget htable

end properties.wasm_module_ok.ConstStageEntry
