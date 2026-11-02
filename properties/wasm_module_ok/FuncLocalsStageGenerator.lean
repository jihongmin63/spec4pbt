import properties.wasm_module_ok.IndexedListStage
import properties.wasm_module_ok.LocalListValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncLocalsStageGenerator

def localsCorrect (c : SpecTec.context) :
    CorrectGen (fun ls : List SpecTec.«local» =>
      LocalListValidation.allLocalsValid c ls = true) :=
  IndexedListStage.correct (LocalListValidation.allLocalsValid c)

theorem localsCandidates_mono
    (c : SpecTec.context) (n k : Nat)
    (ls : List SpecTec.«local»)
    (h : ls ∈ IndexedListStage.candidates
      (LocalListValidation.allLocalsValid c) n) :
    ls ∈ IndexedListStage.candidates
      (LocalListValidation.allLocalsValid c) (n + k) :=
  IndexedListStage.candidates_mono
    (LocalListValidation.allLocalsValid c) n k ls h

theorem localsCorrect_nonempty (c : SpecTec.context) :
    Gen.support (localsCorrect c).val [] := by
  rw [(localsCorrect c).property]
  rfl

theorem localsCorrect_sound
    (c : SpecTec.context) (ls : List SpecTec.«local»)
    (h : Gen.support (localsCorrect c).val ls) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.localtype,
        SpecTec.SpecTecCall.«Funcbody_ok:rule:iter:1» c ls⟩)
      0 (.success (.of (LocalListValidation.localTypes ls))) 0 := by
  rw [(localsCorrect c).property] at h
  exact (LocalListValidation.local_iter_success_iff_valid
    c ls (LocalListValidation.localTypes ls) 0 0).2
      ⟨h, rfl, rfl⟩

theorem localsCorrect_complete
    (c : SpecTec.context) (ls : List SpecTec.«local»)
    (out : List SpecTec.localtype) (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.localtype,
        SpecTec.SpecTecCall.«Funcbody_ok:rule:iter:1» c ls⟩)
      n (.success (.of out)) finalSupply) :
    Gen.support (localsCorrect c).val ls := by
  have hr := (LocalListValidation.local_iter_success_iff_valid
    c ls out n finalSupply).1 h
  rw [(localsCorrect c).property]
  exact hr.1

def localsStage : Staged.Stage SpecTec.context
    (List SpecTec.«local») where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c ls => LocalListValidation.allLocalsValid c ls = true
  generate := fun c => (localsCorrect c).val
  always := by
    intro c _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro c ls _ h
    rw [(localsCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c ls _ hv _
    rw [(localsCorrect c).property]
    exact hv

def localsTypedGen (c : SpecTec.context) :
    Gen (List SpecTec.«local» × List SpecTec.localtype) :=
  (localsCorrect c).val >>= fun ls =>
    pure (ls, LocalListValidation.localTypes ls)

theorem localsTyped_support_iff
    (c : SpecTec.context) (ls : List SpecTec.«local»)
    (out : List SpecTec.localtype) :
    Gen.support (localsTypedGen c) (ls, out) ↔
      LocalListValidation.allLocalsValid c ls = true ∧
        out = LocalListValidation.localTypes ls := by
  simp only [localsTypedGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    cases hpure
    rw [(localsCorrect c).property] at hchosen
    exact ⟨hchosen, rfl⟩
  · rintro ⟨hvalid, rfl⟩
    refine ⟨ls, ?_, rfl⟩
    rw [(localsCorrect c).property]
    exact hvalid

def localsTypedStage :
    Staged.Stage SpecTec.context
      (List SpecTec.«local» × List SpecTec.localtype) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    LocalListValidation.allLocalsValid c output.1 = true ∧
      output.2 = LocalListValidation.localTypes output.1
  generate := localsTypedGen
  always := by
    intro c _
    exact ⟨([], []), ⟨rfl, rfl⟩, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(localsTyped_support_iff c output.1 output.2).1 h,
      trivial⟩
  complete := by
    intro c output _ hv _
    exact (localsTyped_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.FuncLocalsStageGenerator
