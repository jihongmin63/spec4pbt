import properties.wasm_module_ok.GlobalsDecision
import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.GlobalsStageGenerator

def globalsValid (c : SpecTec.context)
    (gs : List SpecTec.global) : Bool :=
  (GlobalsDecision.globalsResult c gs).isSome

def globalsCorrect (c : SpecTec.context) :
    CorrectGen (fun gs : List SpecTec.global =>
      globalsValid c gs = true) :=
  IndexedListStage.correct (globalsValid c)

theorem globalsCandidates_mono
    (c : SpecTec.context) (n k : Nat)
    (gs : List SpecTec.global)
    (h : gs ∈ IndexedListStage.candidates (globalsValid c) n) :
    gs ∈ IndexedListStage.candidates
      (globalsValid c) (n + k) :=
  IndexedListStage.candidates_mono (globalsValid c) n k gs h

theorem globalsCorrect_nonempty (c : SpecTec.context) :
    Gen.support (globalsCorrect c).val [] := by
  rw [(globalsCorrect c).property]
  rfl

theorem globalsCorrect_sound
    (c : SpecTec.context) (gs : List SpecTec.global)
    (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hsupport : Gen.support (globalsCorrect c).val gs) :
    ∃ out : SpecTec.context,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Globals_ok c gs⟩)
        n (.success (.of out)) n := by
  rw [(globalsCorrect c).property] at hsupport
  cases hresult : GlobalsDecision.globalsResult c gs with
  | none => simp [globalsValid, hresult] at hsupport
  | some out =>
      exact ⟨out,
        (GlobalsDecision.globals_result_iff_call
          c out gs n n hready hprov hnested).1 ⟨hresult, rfl⟩⟩

theorem globalsCorrect_complete
    (c out : SpecTec.context) (gs : List SpecTec.global)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Globals_ok c gs⟩)
      start (.success (.of out)) finish) :
    Gen.support (globalsCorrect c).val gs := by
  rw [(globalsCorrect c).property]
  have hresult := ((GlobalsDecision.globals_result_iff_call
    c out gs start finish hready hprov hnested).2 hcall).1
  simp [globalsValid, hresult]

def globalsStateGen (c : SpecTec.context) :
    Gen (List SpecTec.global × SpecTec.context) :=
  (globalsCorrect c).val >>= fun gs =>
    pure (gs, (GlobalsDecision.globalsResult c gs).getD c)

theorem globalsState_support_iff
    (c out : SpecTec.context) (gs : List SpecTec.global) :
    Gen.support (globalsStateGen c) (gs, out) ↔
      GlobalsDecision.globalsResult c gs = some out := by
  simp only [globalsStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(globalsCorrect c).property] at hchosen
    cases hresult : GlobalsDecision.globalsResult c chosen with
    | none => simp [globalsValid, hresult] at hchosen
    | some next =>
        simp only [hresult, Option.getD_some] at hpure
        cases hpure
        exact hresult
  · intro hresult
    refine ⟨gs, ?_, ?_⟩
    · rw [(globalsCorrect c).property]
      simp [globalsValid, hresult]
    · simp [hresult]

def globalsStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.global × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c pair =>
    GlobalsDecision.globalsResult c pair.1 = some pair.2
  generate := globalsStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c pair _ hsupport
    exact ⟨(globalsState_support_iff c pair.2 pair.1).1 hsupport,
      trivial⟩
  complete := by
    intro c pair _ hvalid _
    exact (globalsState_support_iff c pair.2 pair.1).2 hvalid

end properties.wasm_module_ok.GlobalsStageGenerator
