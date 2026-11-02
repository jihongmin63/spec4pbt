import properties.wasm_module_ok.TablesDecision
import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.TablesStageGenerator

def tablesValid (c : SpecTec.context)
    (gs : List SpecTec.table) : Bool :=
  (TablesDecision.tablesResult c gs).isSome

def tablesCorrect (c : SpecTec.context) :
    CorrectGen (fun gs : List SpecTec.table =>
      tablesValid c gs = true) :=
  IndexedListStage.correct (tablesValid c)

theorem tablesCandidates_mono
    (c : SpecTec.context) (n k : Nat)
    (gs : List SpecTec.table)
    (h : gs ∈ IndexedListStage.candidates (tablesValid c) n) :
    gs ∈ IndexedListStage.candidates
      (tablesValid c) (n + k) :=
  IndexedListStage.candidates_mono (tablesValid c) n k gs h

theorem tablesCorrect_nonempty (c : SpecTec.context) :
    Gen.support (tablesCorrect c).val [] := by
  rw [(tablesCorrect c).property]
  rfl

theorem tablesCorrect_sound
    (c : SpecTec.context) (gs : List SpecTec.table)
    (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hsupport : Gen.support (tablesCorrect c).val gs) :
    ∃ out : SpecTec.context,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Tables_ok c gs⟩)
        n (.success (.of out)) n := by
  rw [(tablesCorrect c).property] at hsupport
  cases hresult : TablesDecision.tablesResult c gs with
  | none => simp [tablesValid, hresult] at hsupport
  | some out =>
      exact ⟨out,
        (TablesDecision.tables_result_iff_call
          c out gs n n hready hprov hnested).1 ⟨hresult, rfl⟩⟩

theorem tablesCorrect_complete
    (c out : SpecTec.context) (gs : List SpecTec.table)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Tables_ok c gs⟩)
      start (.success (.of out)) finish) :
    Gen.support (tablesCorrect c).val gs := by
  rw [(tablesCorrect c).property]
  have hresult := ((TablesDecision.tables_result_iff_call
    c out gs start finish hready hprov hnested).2 hcall).1
  simp [tablesValid, hresult]

def tablesStateGen (c : SpecTec.context) :
    Gen (List SpecTec.table × SpecTec.context) :=
  (tablesCorrect c).val >>= fun gs =>
    pure (gs, (TablesDecision.tablesResult c gs).getD c)

theorem tablesState_support_iff
    (c out : SpecTec.context) (gs : List SpecTec.table) :
    Gen.support (tablesStateGen c) (gs, out) ↔
      TablesDecision.tablesResult c gs = some out := by
  simp only [tablesStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(tablesCorrect c).property] at hchosen
    cases hresult : TablesDecision.tablesResult c chosen with
    | none => simp [tablesValid, hresult] at hchosen
    | some next =>
        simp only [hresult, Option.getD_some] at hpure
        cases hpure
        exact hresult
  · intro hresult
    refine ⟨gs, ?_, ?_⟩
    · rw [(tablesCorrect c).property]
      simp [tablesValid, hresult]
    · simp [hresult]

def tablesStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.table × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c pair =>
    TablesDecision.tablesResult c pair.1 = some pair.2
  generate := tablesStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c pair _ hsupport
    exact ⟨(tablesState_support_iff c pair.2 pair.1).1 hsupport,
      trivial⟩
  complete := by
    intro c pair _ hvalid _
    exact (tablesState_support_iff c pair.2 pair.1).2 hvalid

end properties.wasm_module_ok.TablesStageGenerator
