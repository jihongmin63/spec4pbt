import pbt.CorrectGen

namespace Spec4Pbt.CorrectGenTests

-- These type checks distinguish the total contract from an Option-valued search.
example : Generator Nat = (Nat → Nat → Nat) := rfl

example (gen : Generator Nat) (value : Nat) :
    Support gen value ↔ ∃ size seed, gen size seed = value := Iff.rfl

example {α : Type} {P : α → Prop} (gen : CorrectGen P) (size seed : Nat) :
    P (gen.val size seed) := gen.sound size seed

example {α : Type} {P : α → Prop} (gen : CorrectGen P) (value : α)
    (valid : P value) : ∃ size seed, gen.val size seed = value :=
  gen.complete value valid

example {α : Type} {P : α → Prop} (gen : Generator α) :
    (∀ value, Support gen value ↔ P value) ↔
      (∀ size seed, P (gen size seed)) ∧
      (∀ value, P value → ∃ size seed, gen size seed = value) :=
  CorrectGen.exact_support_iff gen P

private def sized : CorrectGen (fun _ : Nat => True) :=
  ⟨fun size _ => size, by
    intro value
    exact ⟨fun _ => True.intro, fun _ => ⟨value, 0, rfl⟩⟩⟩

private def picked := CorrectGen.pick (CorrectGen.pure 3) (CorrectGen.pure 5)
private def mapped := CorrectGen.map (fun n : Nat => n + 10) picked
private def paired := CorrectGen.bind sized fun x =>
  CorrectGen.map (fun y => (x, y)) sized
private def converted := CorrectGen.convert (CorrectGen.pure 3)
  (fun value => show value = 3 ↔ 3 = value from eq_comm)

#guard (CorrectGen.pure 3).val 0 0 = 3
#guard (CorrectGen.pure 3).val 12 1000000 = 3
#guard picked.val 0 0 = 3
#guard picked.val 0 1 = 5
#guard picked.val 20 10 = 3
#guard picked.val 20 11 = 5
#guard picked.val 20 1000000 = 3
#guard picked.val 20 1000001 = 5
#guard mapped.val 0 0 = 13
#guard mapped.val 0 1 = 15
#guard paired.val 0 0 = (0, 0)
#guard paired.val 7 0 = (2, 1)
#guard converted.val 0 0 = 3

-- Completeness must combine independent sizes for the outer and inner sampler.
example (x y : Nat) : ∃ size seed, paired.val size seed = (x, y) := by
  apply paired.complete
  exact ⟨x, True.intro, y, True.intro, rfl⟩

-- A total correct generator cannot certify an empty predicate.
example {α : Type} (gen : CorrectGen (fun _ : α => False)) : False :=
  gen.sound 0 0

end Spec4Pbt.CorrectGenTests
