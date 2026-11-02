import properties.wasm_module_ok.GlobalDecision
import properties.wasm_module_ok.IndexedValueStage
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.GlobalStageGenerator

def globalCorrect (c : SpecTec.context) :
    CorrectGen (fun g : SpecTec.global =>
      GlobalDecision.globalValid c g = true) :=
  IndexedValueStage.correct (GlobalDecision.globalValid c)

theorem globalCandidates_mono
    (c : SpecTec.context) (n k : Nat) (g : SpecTec.global)
    (h : g ∈ IndexedValueStage.candidates
      (GlobalDecision.globalValid c) n) :
    g ∈ IndexedValueStage.candidates
      (GlobalDecision.globalValid c) (n + k) :=
  IndexedValueStage.candidates_mono
    (GlobalDecision.globalValid c) n k g h

theorem globalCorrect_sound
    (c : SpecTec.context) (g : SpecTec.global) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hsupport : Gen.support (globalCorrect c).val g) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Global_ok c g⟩)
      n (.success (.of
        {c with GLOBALS := c.GLOBALS ++ [g.GTYPE]})) n := by
  rw [(globalCorrect c).property] at hsupport
  apply (GlobalDecision.global_result_iff_call c
    {c with GLOBALS := c.GLOBALS ++ [g.GTYPE]}
    g n n hready hprov hnested).1
  exact ⟨(GlobalDecision.global_result_iff_valid c _ g).2
    ⟨hsupport, rfl⟩, rfl⟩

theorem globalCorrect_complete
    (c out : SpecTec.context) (g : SpecTec.global)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Global_ok c g⟩)
      start (.success (.of out)) finish) :
    Gen.support (globalCorrect c).val g := by
  rw [(globalCorrect c).property]
  exact ((GlobalDecision.global_result_iff_valid c out g).1
    ((GlobalDecision.global_result_iff_call c out g
      start finish hready hprov hnested).2 hcall).1).1

def globalStateGen (c : SpecTec.context) :
    Gen (SpecTec.global × SpecTec.context) :=
  (globalCorrect c).val >>= fun g =>
    pure (g, {c with GLOBALS := c.GLOBALS ++ [g.GTYPE]})

theorem globalState_support_iff
    (c out : SpecTec.context) (g : SpecTec.global) :
    Gen.support (globalStateGen c) (g, out) ↔
      GlobalDecision.globalResult c g = some out := by
  simp only [globalStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    cases hpure
    rw [(globalCorrect c).property] at hchosen
    exact (GlobalDecision.global_result_iff_valid c _ g).2
      ⟨hchosen, rfl⟩
  · intro hresult
    obtain ⟨hvalid, hout⟩ :=
      (GlobalDecision.global_result_iff_valid c out g).1 hresult
    subst out
    refine ⟨g, ?_, rfl⟩
    rw [(globalCorrect c).property]
    exact hvalid

def globalStateStage :
    Staged.Stage SpecTec.context
      (SpecTec.global × SpecTec.context) where
  entry := fun c => ∃ g out, GlobalDecision.globalResult c g = some out
  nextEntry := fun _ => True
  valid := fun c pair =>
    GlobalDecision.globalResult c pair.1 = some pair.2
  generate := globalStateGen
  always := by
    intro c hentry
    obtain ⟨g, out, hresult⟩ := hentry
    exact ⟨(g, out), hresult, trivial⟩
  sound := by
    intro c pair _ hsupport
    exact ⟨(globalState_support_iff c pair.2 pair.1).1 hsupport,
      trivial⟩
  complete := by
    intro c pair _ hvalid _
    exact (globalState_support_iff c pair.2 pair.1).2 hvalid

end properties.wasm_module_ok.GlobalStageGenerator
