import pbt.CorrectGen

namespace Spec4Pbt.CorrectGenTests

open Gen Gen.CorrectGen

-- The generator is Palamedes's syntax tree, interpreted by its support relation.
example : Gen.support (Raw.Gen.ret (3 : Nat)) 3 := rfl
example : Gen.support (pure (3 : Nat)) 3 := rfl

example (left right : Gen Nat) (value : Nat) :
    Gen.support (Gen.pick left right) value ↔
      Gen.support left value ∨ Gen.support right value := Iff.rfl

example (outer : Gen Nat) (next : Nat → Gen Nat) (value : Nat) :
    Gen.support (outer >>= next) value ↔
      ∃ input, Gen.support outer input ∧ Gen.support (next input) value := Iff.rfl

example (family : Nat → Gen (Option Nat)) (value : Nat) :
    Gen.support (Gen.indexed family) value ↔
      (∀ v n m, Gen.support (family n) (some v) →
        Gen.support (family (n + m)) (some v)) ∧
      ∃ n, Gen.support (family n) (some value) := Iff.rfl

example (condition : Bool) (next : condition → Gen Nat) (value : Nat) :
    Gen.support (Gen.assume condition next) value ↔
      ∃ proof : condition, Gen.support (next proof) value := Iff.rfl

example : Gen.support (Gen.assume true (fun _ => pure (7 : Nat))) 7 := by
  simp

private def oneOrTwo : CorrectGen (fun n : Nat => n = 1 ∨ n = 2) :=
  s_pick (s_pure 1) (s_pure 2)

private def doubled : CorrectGen
    (fun n : Nat => ∃ k, (k = 1 ∨ k = 2) ∧ n = 2 * k) :=
  s_bind oneOrTwo (fun k => s_pure (2 * k))

example : Gen.support doubled.val 2 := by
  rw [doubled.property]
  exact ⟨1, Or.inl rfl, rfl⟩

example : Gen.support doubled.val 4 := by
  rw [doubled.property]
  exact ⟨2, Or.inr rfl, rfl⟩

example : Gen.support Gen.arbNat 137 := by
  rw [Gen.support_arbNat]
  trivial

end Spec4Pbt.CorrectGenTests
