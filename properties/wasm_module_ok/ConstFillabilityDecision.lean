import properties.wasm_module_ok.ConstProductiveDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFillabilityDecision

/-- Finite, executable productive-closure decision for a constant expression. -/
def constFillable (c : SpecTec.context) (t : SpecTec.valtype) : Bool :=
  ConstProductiveFillability.productiveFillable c t

theorem const_fillable_iff_mem
    (c : SpecTec.context) (t : SpecTec.valtype) :
    constFillable c t = true ↔
      t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
        (ConstMatchAwareClosure.sourcesOf c
          (FiniteClosure.iterate
            (ConstProductiveClosure.productiveStep c)
            (FiniteValidTypes.candidateUniverse c).card)) := by
  simp only [constFillable,
    ConstProductiveFillability.productiveFillable,
    ConstProductiveFillability.productiveClosure, decide_eq_true_eq]

/-- The decision records a produced type and an exact executable match to
the requested target. This is the witness interface for the converse proof. -/
theorem const_fillable_iff_witness
    (c : SpecTec.context) (t : SpecTec.valtype) :
    constFillable c t = true ↔
      t ∈ ConstFieldCandidate.extendedCandidateUniverse c ∧
      ∃ u ∈ ConstMatchAwareClosure.sourcesOf c
          (FiniteClosure.iterate
            (ConstProductiveClosure.productiveStep c)
            (FiniteValidTypes.candidateUniverse c).card),
        CandidateValMatch.candidateValMatch c u t = true := by
  exact (const_fillable_iff_mem c t).trans
    (ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
      c (ConstMatchAwareClosure.sourcesOf c
        (FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep c)
          (FiniteValidTypes.candidateUniverse c).card)) t)

theorem const_ok_implies_fillable
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype) (xs : SpecTec.const)
    (start finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) finish)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    constFillable c t = true := by
  exact (const_fillable_iff_mem c t).2
    (ConstOkProductiveClosure.const_ok_target_in_fixed_productive_saturation
      m tr c hc t xs start finish hconst htarget htable)

theorem const_fillable_iff_const_ok
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    constFillable c t = true ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
          start (.success (.of ())) finish := by
  exact ConstProductiveDecision.productive_fillable_iff_const_ok_any_counters
    m tr c hc t htarget htable

theorem no_const_ok_of_not_fillable
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t)
    (hfalse : constFillable c t = false) :
    ¬ ∃ (xs : SpecTec.const) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        start (.success (.of ())) finish := by
  rintro ⟨xs, start, finish, hconst⟩
  have htrue := const_ok_implies_fillable
    m tr c hc t xs start finish hconst htarget htable
  simp [hfalse] at htrue

end properties.wasm_module_ok.ConstFillabilityDecision
