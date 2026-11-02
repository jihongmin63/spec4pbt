/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositivePlans
import properties.wasm_module_ok.PositiveErasure
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTecExecution
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def run (fuel : Nat) {α : Type} (p : ExecutablePlan Call α) (s : Nat) : RunResult α :=
  runEval program (PrimitiveRunner.unavailable program) fuel p s

theorem mono {n k : Nat} (le : n ≤ k) {α : Type}
    (p : ExecutablePlan Call α) (s : Nat) (o : Outcome α) (t : Nat)
    (h : run n p s = .done o t) : run k p s = .done o t :=
  runEval_mono program (PrimitiveRunner.unavailable program) le p s o t h

theorem complete
    (bodyCorrect : ∀ {α : Type} (c : Call α),
      erase (body c) = SpecTec.specTecBody ⟨_, toOriginal c⟩)
    {raw : Plan SpecTec.SpecTecRequest} {s t : Nat} {o : Outcome Value}
    (h : Eval SpecTec.specTecProgram raw s o t) :
    ∀ {α : Type} (p : ExecutablePlan Call α), erase p = raw →
      ∃ (n : Nat) (typed : Outcome α), typed.pack = o ∧ run n p s = .done typed t := by
  induction h with
  | pure v =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .success v, rfl, rfl⟩
  | unmatch =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .unmatch, rfl, rfl⟩
  | abort msg =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .abort msg, rfl, rfl⟩
  | freshId =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .success _, rfl, rfl⟩
  | primitive h => exact False.elim h
  | guard_true h =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .success (), rfl, by simp [run, runEval, h]⟩
  | guard_false h =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    exact ⟨1, .unmatch, rfl, by simp [run, runEval, h]⟩
  | call h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i c
    obtain ⟨n, o, ho, hr⟩ := ih (body c) (bodyCorrect c)
    exact ⟨n + 1, o, ho, hr⟩
  | bind_success h₁ h₂ ih₁ ih₂ =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n₁, o₁, he₁, hr₁⟩ := ih₁ p rfl
    cases o₁ with
    | unmatch => cases he₁
    | abort msg => cases he₁
    | success v =>
      cases he₁
      obtain ⟨n₂, o₂, he₂, hr₂⟩ := ih₂ (k _) rfl
      have hr₁' := mono (Nat.le_max_left n₁ n₂) p _ _ _ hr₁
      have hr₂' := mono (Nat.le_max_right n₁ n₂) _ _ _ _ hr₂
      refine ⟨max n₁ n₂ + 1, o₂, he₂, ?_⟩
      simp only [run] at hr₁' hr₂' ⊢
      simp only [runEval, hr₁', hr₂']
  | bind_unmatch h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed <;> cases he
    refine ⟨n + 1, .unmatch, rfl, ?_⟩
    simp only [run] at hr ⊢
    simp only [runEval, hr]
  | bind_abort h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed <;> cases he
    refine ⟨n + 1, .abort _, rfl, ?_⟩
    simp only [run] at hr ⊢
    simp only [runEval, hr]
  | orElse_success h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed with
    | unmatch => cases he
    | abort msg => cases he
    | success v =>
      refine ⟨n + 1, .success v, he, ?_⟩
      simp only [run] at hr ⊢
      simp only [runEval, hr]
  | orElse_unmatch h₁ h₂ ih₁ ih₂ =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n₁, typed, he₁, hr₁⟩ := ih₁ p rfl
    cases typed <;> cases he₁
    obtain ⟨n₂, o₂, he₂, hr₂⟩ := ih₂ (k ()) rfl
    have hr₁' := mono (Nat.le_max_left n₁ n₂) p _ _ _ hr₁
    have hr₂' := mono (Nat.le_max_right n₁ n₂) (k ()) _ _ _ hr₂
    refine ⟨max n₁ n₂ + 1, o₂, he₂, ?_⟩
    simp only [run] at hr₁' hr₂' ⊢
    simp only [runEval, hr₁', hr₂']
  | orElse_abort h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p k
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed <;> cases he
    refine ⟨n + 1, .abort _, rfl, ?_⟩
    simp only [run] at hr ⊢
    simp only [runEval, hr]
  | notHold_success h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed <;> cases he
    refine ⟨n + 1, .success (), rfl, ?_⟩
    simp only [run] at hr ⊢
    simp only [runEval, hr]
  | notHold_unmatch h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed with
    | unmatch => cases he
    | abort msg => cases he
    | success v =>
      refine ⟨n + 1, .unmatch, rfl, ?_⟩
      simp only [run] at hr ⊢
      simp only [runEval, hr]
  | notHold_abort h ih =>
    intro α p hp
    cases p <;> simp only [erase] at hp <;> cases hp
    rename_i p
    obtain ⟨n, typed, he, hr⟩ := ih p rfl
    cases typed <;> cases he
    refine ⟨n + 1, .abort _, rfl, ?_⟩
    simp only [run] at hr ⊢
    simp only [runEval, hr]
end properties.wasm_module_ok.PositiveRuntime
