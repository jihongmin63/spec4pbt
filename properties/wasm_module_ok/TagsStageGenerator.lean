import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.TagsValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.TagsStageGenerator

def tagsValid (c : SpecTec.context)
    (ms : List SpecTec.tag) : Bool :=
  (TagsValidation.tagsResult c ms).isSome

def tagsCorrect (c : SpecTec.context) :
    CorrectGen (fun ms : List SpecTec.tag =>
      tagsValid c ms = true) :=
  IndexedListStage.correct (tagsValid c)

theorem tagsCorrect_nonempty (c : SpecTec.context) :
    Gen.support (tagsCorrect c).val [] := by
  rw [(tagsCorrect c).property]
  rfl

theorem tagsCorrect_sound
    (c : SpecTec.context) (ms : List SpecTec.tag)
    (h : Gen.support (tagsCorrect c).val ms) :
    ∃ result : SpecTec.context,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Tags_ok c ms⟩)
        0 (.success (.of result)) 0 := by
  rw [(tagsCorrect c).property] at h
  cases hr : TagsValidation.tagsResult c ms with
  | none => simp [tagsValid, hr] at h
  | some result =>
      exact ⟨result,
        (TagsValidation.tags_success_iff_result
          c ms result 0 0).2 ⟨hr, rfl⟩⟩

theorem tagsCorrect_complete
    (c : SpecTec.context) (ms : List SpecTec.tag)
    (result : SpecTec.context)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Tags_ok c ms⟩)
      0 (.success (.of result)) 0) :
    Gen.support (tagsCorrect c).val ms := by
  have hr := (TagsValidation.tags_success_iff_result
    c ms result 0 0).1 h
  rw [(tagsCorrect c).property]
  simp [tagsValid, hr.1]

def tagsStage : Staged.Stage SpecTec.context
    (List SpecTec.tag) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c ms => tagsValid c ms = true
  generate := fun c => (tagsCorrect c).val
  always := by
    intro c _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro c ms _ h
    rw [(tagsCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c ms _ hv _
    rw [(tagsCorrect c).property]
    exact hv

def tagsStateGen (c : SpecTec.context) :
    Gen (List SpecTec.tag × SpecTec.context) :=
  (tagsCorrect c).val >>= fun ms =>
    pure (ms, (TagsValidation.tagsResult c ms).getD c)

theorem tagsState_support_iff
    (c : SpecTec.context) (ms : List SpecTec.tag)
    (out : SpecTec.context) :
    Gen.support (tagsStateGen c) (ms, out) ↔
      TagsValidation.tagsResult c ms = some out := by
  simp only [tagsStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(tagsCorrect c).property] at hchosen
    cases hr : TagsValidation.tagsResult c chosen with
    | none => simp [tagsValid, hr] at hchosen
    | some result =>
        simp only [hr, Option.getD_some] at hpure
        cases hpure
        exact hr
  · intro hr
    refine ⟨ms, ?_, ?_⟩
    · rw [(tagsCorrect c).property]
      simp [tagsValid, hr]
    · simp [hr]

def tagsStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.tag × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    TagsValidation.tagsResult c output.1 = some output.2
  generate := tagsStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(tagsState_support_iff c output.1 output.2).1 h, trivial⟩
  complete := by
    intro c output _ hv _
    exact (tagsState_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.TagsStageGenerator
