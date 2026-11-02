import Spec4Pbt.CorrectGen
import properties.wasm_module_ok.StartDecision
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.StartStageGenerator

def chooseStarts : List SpecTec.start → Gen (Option SpecTec.start)
  | [] => pure none
  | s :: rest => Gen.pick (pure (some s)) (chooseStarts rest)

theorem chooseStarts_support_none (xs : List SpecTec.start) :
    Gen.support (chooseStarts xs) none := by
  induction xs with
  | nil => simp [chooseStarts]
  | cons s rest ih => simp [chooseStarts, ih]

theorem chooseStarts_support_some
    (xs : List SpecTec.start) (s : SpecTec.start) :
    Gen.support (chooseStarts xs) (some s) ↔ s ∈ xs := by
  induction xs with
  | nil => simp [chooseStarts]
  | cons head rest ih => simp [chooseStarts, ih]

def candidates (c : SpecTec.context) : List SpecTec.start :=
  ((List.range c.FUNCS.length).map
    (fun i => (⟨i⟩ : SpecTec.start))).filter
      (fun s => StartDecision.startValid c (some s))

theorem mem_candidates_iff
    (c : SpecTec.context) (s : SpecTec.start) :
    s ∈ candidates c ↔
      StartDecision.startValid c (some s) = true := by
  simp only [candidates, List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, hv⟩
    exact hv
  · intro hv
    obtain ⟨dt, hget, _⟩ :=
      (StartDecision.start_some_valid_iff c s).mp hv
    have hlt : s.SFUNC < c.FUNCS.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    exact ⟨⟨s.SFUNC, hlt, by cases s; rfl⟩, hv⟩

def startCorrect (c : SpecTec.context) :
    CorrectGen (fun s : Option SpecTec.start =>
      StartDecision.startValid c s = true) := by
  refine ⟨chooseStarts (candidates c), ?_⟩
  funext s
  cases s with
  | none =>
      exact propext ⟨fun _ => rfl,
        fun _ => chooseStarts_support_none (candidates c)⟩
  | some s =>
      exact propext ((chooseStarts_support_some (candidates c) s).trans
        (mem_candidates_iff c s))

theorem startCorrect_nonempty (c : SpecTec.context) :
    Gen.support (startCorrect c).val none :=
  chooseStarts_support_none (candidates c)

theorem startCorrect_sound
    (c : SpecTec.context) (s : Option SpecTec.start)
    (h : Gen.support (startCorrect c).val s) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c s⟩)
      0 (.success (.of ())) 0 := by
  apply (StartDecision.start_success_iff_valid c s 0 0).2
  rw [(startCorrect c).property] at h
  exact ⟨h, rfl⟩

theorem startCorrect_complete
    (c : SpecTec.context) (s : Option SpecTec.start)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c s⟩)
      0 (.success (.of ())) 0) :
    Gen.support (startCorrect c).val s := by
  have hv := (StartDecision.start_success_iff_valid c s 0 0).1 h
  rw [(startCorrect c).property]
  exact hv.1

def startStage :
    Staged.Stage SpecTec.context (Option SpecTec.start) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c s => StartDecision.startValid c s = true
  generate := fun c => (startCorrect c).val
  always := by
    intro c _
    exact ⟨none, rfl, trivial⟩
  sound := by
    intro c s _ h
    rw [(startCorrect c).property] at h
    exact ⟨h, trivial⟩
  complete := by
    intro c s _ hv _
    rw [(startCorrect c).property]
    exact hv

def startStateGen (c : SpecTec.context) :
    Gen (Option SpecTec.start × SpecTec.context) :=
  (startCorrect c).val >>= fun start => pure (start, c)

theorem startState_support_iff
    (c : SpecTec.context) (start : Option SpecTec.start)
    (out : SpecTec.context) :
    Gen.support (startStateGen c) (start, out) ↔
      StartDecision.startValid c start = true ∧ out = c := by
  simp only [startStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    rw [(startCorrect c).property] at hchosen
    cases hpure
    exact ⟨hchosen, rfl⟩
  · rintro ⟨hv, hout⟩
    subst out
    refine ⟨start, ?_, rfl⟩
    rw [(startCorrect c).property]
    exact hv

def startStateStage :
    Staged.Stage SpecTec.context
      (Option SpecTec.start × SpecTec.context) where
  entry := fun _ => True
  nextEntry := fun _ => True
  valid := fun c output =>
    StartDecision.startValid c output.1 = true ∧ output.2 = c
  generate := startStateGen
  always := by
    intro c _
    exact ⟨(none, c), ⟨rfl, rfl⟩, trivial⟩
  sound := by
    intro c output _ h
    exact ⟨(startState_support_iff c output.1 output.2).1 h, trivial⟩
  complete := by
    intro c output _ hv _
    exact (startState_support_iff c output.1 output.2).2 hv

end properties.wasm_module_ok.StartStageGenerator
