import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.ConstStageDecision
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExpressionStageGenerator

/-- An indexed choice among exactly the constant expressions accepted by the
executable translated-expression decision. -/
def expressionCorrect (c : SpecTec.context) (t : SpecTec.valtype) :
    CorrectGen (fun xs : SpecTec.const =>
      ConstExpressionDecision.constantExpressionResult c t xs = true) :=
  IndexedListStage.correct
    (ConstExpressionDecision.constantExpressionResult c t)

theorem expressionCandidates_mono
    (c : SpecTec.context) (t : SpecTec.valtype)
    (n k : Nat) (xs : SpecTec.const)
    (h : xs ∈ IndexedListStage.candidates
      (ConstExpressionDecision.constantExpressionResult c t) n) :
    xs ∈ IndexedListStage.candidates
      (ConstExpressionDecision.constantExpressionResult c t) (n + k) :=
  IndexedListStage.candidates_mono
    (ConstExpressionDecision.constantExpressionResult c t) n k xs h

theorem expressionCorrect_sound
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htable : CandidateValMatch.InTableVal c t)
    (h : Gen.support (expressionCorrect c t).val xs) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      n (.success (.of ())) n := by
  rw [(expressionCorrect c t).property] at h
  exact (ConstExpressionDecision.constant_expression_result_iff_const_ok
    c t xs n hready hprov hnested htable).1 h

theorem expressionCorrect_complete
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htable : CandidateValMatch.InTableVal c t)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    Gen.support (expressionCorrect c t).val xs := by
  rw [(expressionCorrect c t).property]
  exact (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters
    c t xs start finish hready hprov hnested htable).2 h |>.1

def expressionStage :
    Staged.Stage (SpecTec.context × SpecTec.valtype) SpecTec.const where
  entry := fun input => ∃ xs : SpecTec.const,
    ConstExpressionDecision.constantExpressionResult input.1 input.2 xs = true
  nextEntry := fun _ => True
  valid := fun input xs =>
    ConstExpressionDecision.constantExpressionResult input.1 input.2 xs = true
  generate := fun input => (expressionCorrect input.1 input.2).val
  always := by
    intro input hentry
    obtain ⟨xs, hvalid⟩ := hentry
    exact ⟨xs, hvalid, trivial⟩
  sound := by
    intro input xs _ hsupport
    rw [(expressionCorrect input.1 input.2).property] at hsupport
    exact ⟨hsupport, trivial⟩
  complete := by
    intro input xs _ hvalid _
    rw [(expressionCorrect input.1 input.2).property]
    exact hvalid

theorem expression_stage_entry_iff_fillable
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    expressionStage.entry (c, t) ↔
      ConstStageEntry.HasConstContinuation c t := by
  exact (ConstStageDecision.has_const_continuation_iff_expression_result
    m tr c hc t htarget htable).symm

end properties.wasm_module_ok.ConstExpressionStageGenerator
