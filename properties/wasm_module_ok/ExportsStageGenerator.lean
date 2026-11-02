import Spec4Pbt.CorrectGen
import properties.wasm_module_ok.Enumeration
import properties.wasm_module_ok.ExportsValidation
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.ExportsStageGenerator

def chooseList {α : Type} : List α → Gen (Option α)
  | [] => pure none
  | a :: rest => Gen.pick (pure (some a)) (chooseList rest)

theorem chooseList_support_some {α : Type}
    (xs : List α) (a : α) :
    Gen.support (chooseList xs) (some a) ↔ a ∈ xs := by
  induction xs with
  | nil => simp [chooseList]
  | cons head rest ih => simp [chooseList, ih]

def valid (c : SpecTec.context) (names : SpecTec.nameset)
    (es : List SpecTec.«export») : Bool :=
  (ExportsValidation.exportsResult c names es).isSome

def candidates (c : SpecTec.context) (names : SpecTec.nameset)
    (n : Nat) : List (List SpecTec.«export») :=
  (Enumeration.decodeCandidates (α := List SpecTec.«export») n).filter
    (valid c names)

theorem candidates_mono
    (c : SpecTec.context) (names : SpecTec.nameset)
    (n k : Nat) (es : List SpecTec.«export»)
    (h : es ∈ candidates c names n) :
    es ∈ candidates c names (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k es h.1, h.2⟩

def exportGen (c : SpecTec.context) (names : SpecTec.nameset) :
    Gen (List SpecTec.«export») :=
  Gen.indexed (fun n => chooseList (candidates c names n))

theorem exportGen_support_iff
    (c : SpecTec.context) (names : SpecTec.nameset)
    (es : List SpecTec.«export») :
    Gen.support (exportGen c names) es ↔ valid c names es = true := by
  rw [exportGen, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hm := (chooseList_support_some (candidates c names n) es).mp hn
    exact (List.mem_filter.mp hm).2
  · intro hv
    constructor
    · intro e n k hn
      apply (chooseList_support_some (candidates c names (n + k)) e).2
      exact candidates_mono c names n k e
        ((chooseList_support_some (candidates c names n) e).1 hn)
    · obtain ⟨n, hn⟩ :=
        Enumeration.decodeCandidates_complete es
      exact ⟨n,
        (chooseList_support_some (candidates c names n) es).2
          ((List.mem_filter).2 ⟨hn, hv⟩)⟩

def exportCorrect (c : SpecTec.context) (names : SpecTec.nameset) :
    CorrectGen (fun es : List SpecTec.«export» =>
      valid c names es = true) := by
  refine ⟨exportGen c names, ?_⟩
  funext es
  exact propext (exportGen_support_iff c names es)

theorem exportCorrect_nonempty
    (c : SpecTec.context) (names : SpecTec.nameset) :
    Gen.support (exportCorrect c names).val [] := by
  rw [(exportCorrect c names).property]
  rfl

theorem exportCorrect_sound
    (c : SpecTec.context) (names : SpecTec.nameset)
    (es : List SpecTec.«export»)
    (h : Gen.support (exportCorrect c names).val es) :
    ∃ result : SpecTec.nameset,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.nameset,
          SpecTec.SpecTecCall.Exports_ok c names es⟩)
        0 (.success (.of result)) 0 := by
  rw [(exportCorrect c names).property] at h
  cases hr : ExportsValidation.exportsResult c names es with
  | none => simp [valid, hr] at h
  | some result =>
      exact ⟨result,
        (ExportsValidation.exports_success_iff_result
          c names es result 0 0).2 ⟨hr, rfl⟩⟩

theorem exportCorrect_complete
    (c : SpecTec.context) (names : SpecTec.nameset)
    (es : List SpecTec.«export»)
    (result : SpecTec.nameset)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.nameset,
        SpecTec.SpecTecCall.Exports_ok c names es⟩)
        0 (.success (.of result)) 0) :
    Gen.support (exportCorrect c names).val es := by
  have hr := (ExportsValidation.exports_success_iff_result
    c names es result 0 0).1 h
  rw [(exportCorrect c names).property]
  simp [valid, hr.1]

def exportsStage :
    Staged.Stage (SpecTec.context × SpecTec.nameset)
      (List SpecTec.«export») where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun input es => valid input.1 input.2 es = true
  generate := fun input => (exportCorrect input.1 input.2).val
  always := by
    intro input _
    exact ⟨[], rfl, trivial⟩
  sound := by
    intro input es _ h
    rw [(exportCorrect input.1 input.2).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro input es _ hv _
    rw [(exportCorrect input.1 input.2).property]
    exact hv

def exportsStateGen (c : SpecTec.context)
    (names : SpecTec.nameset) :
    Gen (List SpecTec.«export» × SpecTec.nameset) :=
  (exportCorrect c names).val >>= fun es =>
    pure (es, (ExportsValidation.exportsResult c names es).getD names)

theorem exportsState_support_iff
    (c : SpecTec.context) (names : SpecTec.nameset)
    (es : List SpecTec.«export») (out : SpecTec.nameset) :
    Gen.support (exportsStateGen c names) (es, out) ↔
      ExportsValidation.exportsResult c names es = some out := by
  simp only [exportsStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(exportCorrect c names).property] at hchosen
    cases hr : ExportsValidation.exportsResult c names chosen with
    | none => simp [valid, hr] at hchosen
    | some result =>
        simp only [hr, Option.getD_some] at hpure
        cases hpure
        exact hr
  · intro hr
    refine ⟨es, ?_, ?_⟩
    · rw [(exportCorrect c names).property]
      simp [valid, hr]
    · simp [hr]

def exportsStateStage :
    Staged.Stage (SpecTec.context × SpecTec.nameset)
      (List SpecTec.«export» × SpecTec.nameset) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun input output =>
    ExportsValidation.exportsResult input.1 input.2 output.1 =
      some output.2
  generate := fun input => exportsStateGen input.1 input.2
  always := by
    intro input _
    exact ⟨([], input.2), rfl, trivial⟩
  sound := by
    intro input output _ h
    exact ⟨(exportsState_support_iff
      input.1 input.2 output.1 output.2).1 h, trivial⟩
  complete := by
    intro input output _ hv _
    exact (exportsState_support_iff
      input.1 input.2 output.1 output.2).2 hv

end properties.wasm_module_ok.ExportsStageGenerator
