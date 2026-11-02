import properties.wasm_module_ok.ConstProductiveFillability
import properties.wasm_module_ok.ConstOkProductiveClosure
import properties.wasm_module_ok.ModuleCandidateBot

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstProductiveDecision

theorem trace_no_bot_at
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8]) :
    SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    ModuleCandidateBot.trace_no_bot_candidates m tr
  simp at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc
  · rw [hc]; exact h0
  · rw [hc]; exact h1
  · rw [hc]; exact h2
  · rw [hc]; exact h3
  · rw [hc]; exact h4
  · rw [hc]; exact h5
  · rw [hc]; exact h6
  · rw [hc]; exact h7
  · rw [hc]; exact h8

/-- The finite productive decision has an actual constant expression witness
in every validated module stage where the target belongs to its explicit
candidate and table domains. -/
theorem productive_fillable_iff_const_ok
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    ConstProductiveFillability.productiveFillable c t = true ↔
      ∃ (xs : SpecTec.const) (n : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
          n (.success (.of ())) n := by
  constructor
  · intro hfill
    exact ConstProductiveFillability.productive_fillable_const_witness
      c t hfill (trace_no_bot_at m tr c hc)
      (CandidateTraceReady.trace_ready_at m tr c hc)
      (CandidateTraceReady.trace_provenance_at m tr c hc)
      (ConstTraceNestedReady.trace_nested_ready_at m tr c hc)
      htable
  · rintro ⟨xs, n, hconst⟩
    have hmem :=
      ConstOkProductiveClosure.const_ok_target_in_fixed_productive_saturation
        m tr c hc t xs n n hconst htarget htable
    simpa only [ConstProductiveFillability.productiveFillable,
      ConstProductiveFillability.productiveClosure,
      decide_eq_true_eq] using hmem

/-- The same decision covers every successful translated trace, even if its
initial and final execution counters differ. -/
theorem productive_fillable_iff_const_ok_any_counters
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    ConstProductiveFillability.productiveFillable c t = true ↔
      ∃ (xs : SpecTec.const) (start finish : Nat),
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
          start (.success (.of ())) finish := by
  constructor
  · intro hfill
    obtain ⟨xs, n, hconst⟩ :=
      (productive_fillable_iff_const_ok
        m tr c hc t htarget htable).1 hfill
    exact ⟨xs, n, n, hconst⟩
  · rintro ⟨xs, start, finish, hconst⟩
    have hmem :=
      ConstOkProductiveClosure.const_ok_target_in_fixed_productive_saturation
        m tr c hc t xs start finish hconst htarget htable
    simpa only [ConstProductiveFillability.productiveFillable,
      ConstProductiveFillability.productiveClosure,
      decide_eq_true_eq] using hmem

end properties.wasm_module_ok.ConstProductiveDecision
