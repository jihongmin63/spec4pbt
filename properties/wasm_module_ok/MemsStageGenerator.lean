import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.MemsValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.MemsStageGenerator

def memsValid (c : SpecTec.context)
    (ms : List SpecTec.memory) : Bool :=
  (MemsValidation.memsResult c ms).isSome

def memsCorrect (c : SpecTec.context) :
    CorrectGen (fun ms : List SpecTec.memory =>
      memsValid c ms = true) :=
  IndexedListStage.correct (memsValid c)

theorem memsCorrect_nonempty (c : SpecTec.context) :
    Gen.support (memsCorrect c).val [] := by
  rw [(memsCorrect c).property]
  rfl

theorem memsCorrect_sound
    (c : SpecTec.context) (ms : List SpecTec.memory)
    (h : Gen.support (memsCorrect c).val ms) :
    ∃ result : SpecTec.context,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Mems_ok c ms⟩)
        0 (.success (.of result)) 0 := by
  rw [(memsCorrect c).property] at h
  cases hr : MemsValidation.memsResult c ms with
  | none => simp [memsValid, hr] at h
  | some result =>
      exact ⟨result,
        (MemsValidation.mems_success_iff_result
          c ms result 0 0).2 ⟨hr, rfl⟩⟩

theorem memsCorrect_complete
    (c : SpecTec.context) (ms : List SpecTec.memory)
    (result : SpecTec.context)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Mems_ok c ms⟩)
      0 (.success (.of result)) 0) :
    Gen.support (memsCorrect c).val ms := by
  have hr := (MemsValidation.mems_success_iff_result
    c ms result 0 0).1 h
  rw [(memsCorrect c).property]
  simp [memsValid, hr.1]

def memsStage : Staged.Stage SpecTec.context
    (List SpecTec.memory) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c ms => memsValid c ms = true
  generate := fun c => (memsCorrect c).val
  always := by
    intro c _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro c ms _ h
    rw [(memsCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c ms _ hv _
    rw [(memsCorrect c).property]
    exact hv

def memsStateGen (c : SpecTec.context) :
    Gen (List SpecTec.memory × SpecTec.context) :=
  (memsCorrect c).val >>= fun ms =>
    pure (ms, (MemsValidation.memsResult c ms).getD c)

theorem memsState_support_iff
    (c : SpecTec.context) (ms : List SpecTec.memory)
    (out : SpecTec.context) :
    Gen.support (memsStateGen c) (ms, out) ↔
      MemsValidation.memsResult c ms = some out := by
  simp only [memsStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(memsCorrect c).property] at hchosen
    cases hr : MemsValidation.memsResult c chosen with
    | none => simp [memsValid, hr] at hchosen
    | some result =>
        simp only [hr, Option.getD_some] at hpure
        cases hpure
        exact hr
  · intro hr
    refine ⟨ms, ?_, ?_⟩
    · rw [(memsCorrect c).property]
      simp [memsValid, hr]
    · simp [hr]

def memsStateStage :
    Staged.Stage SpecTec.context
      (List SpecTec.memory × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    MemsValidation.memsResult c output.1 = some output.2
  generate := memsStateGen
  always := by
    intro c _
    exact ⟨([], c), rfl, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(memsState_support_iff c output.1 output.2).1 h, trivial⟩
  complete := by
    intro c output _ hv _
    exact (memsState_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.MemsStageGenerator
