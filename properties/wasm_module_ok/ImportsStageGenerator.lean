import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.ImportsValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.ImportsStageGenerator

def importsValid (c : SpecTec.context)
    (ms : List SpecTec.«import») : Bool :=
  (ImportsValidation.importsResult c ms).isSome

def importsCorrect (c : SpecTec.context) :
    CorrectGen (fun ms : List SpecTec.«import» =>
      importsValid c ms = true) :=
  IndexedListStage.correct (importsValid c)

theorem importsCorrect_nonempty (c : SpecTec.context) :
    Gen.support (importsCorrect c).val [] := by
  rw [(importsCorrect c).property]
  rfl

theorem importsCorrect_sound
    (c : SpecTec.context) (ms : List SpecTec.«import»)
    (h : Gen.support (importsCorrect c).val ms) :
    ∃ result : SpecTec.context,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Imports_ok c ms⟩)
        0 (.success (.of result)) 0 := by
  rw [(importsCorrect c).property] at h
  cases hr : ImportsValidation.importsResult c ms with
  | none => simp [importsValid, hr] at h
  | some result =>
      exact ⟨result,
        (ImportsValidation.imports_success_iff_result
          c ms result 0 0).2 ⟨hr, rfl⟩⟩

theorem importsCorrect_complete
    (c : SpecTec.context) (ms : List SpecTec.«import»)
    (result : SpecTec.context)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Imports_ok c ms⟩)
      0 (.success (.of result)) 0) :
    Gen.support (importsCorrect c).val ms := by
  have hr := (ImportsValidation.imports_success_iff_result
    c ms result 0 0).1 h
  rw [(importsCorrect c).property]
  simp [importsValid, hr.1]

def importsStage : Staged.Stage SpecTec.context
    (List SpecTec.«import») where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c ms => importsValid c ms = true
  generate := fun c => (importsCorrect c).val
  always := by
    intro c _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro c ms _ h
    rw [(importsCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c ms _ hv _
    rw [(importsCorrect c).property]
    exact hv

def importsStateGen (c : SpecTec.context) :
    Gen (List SpecTec.«import» × SpecTec.context) :=
  (importsCorrect c).val >>= fun ms =>
    pure (ms, (ImportsValidation.importsResult c ms).getD c)

theorem importsState_support_iff
    (c : SpecTec.context) (ms : List SpecTec.«import»)
    (out : SpecTec.context) :
    Gen.support (importsStateGen c) (ms, out) ↔
      ImportsValidation.importsResult c ms = some out := by
  simp only [importsStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(importsCorrect c).property] at hchosen
    cases hr : ImportsValidation.importsResult c chosen with
    | none => simp [importsValid, hr] at hchosen
    | some result =>
        simp only [hr, Option.getD_some] at hpure
        cases hpure
        exact hr
  · intro hr
    refine ⟨ms, ?_, ?_⟩
    · rw [(importsCorrect c).property]
      simp [importsValid, hr]
    · simp [hr]

def importsStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.«import» × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    ImportsValidation.importsResult c output.1 = some output.2
  generate := importsStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(importsState_support_iff c output.1 output.2).1 h, trivial⟩
  complete := by
    intro c output _ hv _
    exact (importsState_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.ImportsStageGenerator
