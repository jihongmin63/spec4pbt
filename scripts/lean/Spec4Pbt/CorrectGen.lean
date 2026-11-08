import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Data.Nat
import Palamedes.Sample

/-!
The generator core and its proof rules come directly from Palamedes.
Import this module to use its syntax-tree `Gen`, exact `Gen.support`,
`CorrectGen`, manual synthesis rules, and sampler.
-/

namespace Gen

/-- Every indexed node is monotone in its successful outputs, including nodes
inside branches and continuations. -/
def IndexLawful : Gen α → Prop
  | .ret _ => True
  | .pick x y => IndexLawful x ∧ IndexLawful y
  | .bind x f => IndexLawful x ∧ ∀ a, IndexLawful (f a)
  | .assume b f => ∀ h : b, IndexLawful (f h)
  | .indexed f => (∀ n, IndexLawful (f n)) ∧
      ∀ a n k, support (f n) (some a) → support (f (n + k)) (some a)

namespace IndexLawful

@[simp] theorem pure (a : α) : IndexLawful (Pure.pure a : Gen α) := trivial

@[simp] theorem pick (x y : Gen α) :
    IndexLawful (Gen.pick x y) ↔ IndexLawful x ∧ IndexLawful y := Iff.rfl

@[simp] theorem bind (x : Gen α) (f : α → Gen β) :
    IndexLawful (x >>= f) ↔ IndexLawful x ∧ ∀ a, IndexLawful (f a) := Iff.rfl

@[simp] theorem map (f : α → β) (x : Gen α) :
    IndexLawful (f <$> x) ↔ IndexLawful x := by
  change (IndexLawful x ∧ ∀ _, True) ↔ IndexLawful x
  simp

@[simp] theorem arbNatAux (n : Nat) : IndexLawful (Gen.arbNatAux n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simpa only [Gen.arbNatAux, pick, pure, map, true_and] using ih

@[simp] theorem arbNat : IndexLawful Gen.arbNat := by
  unfold Gen.arbNat
  exact ⟨arbNatAux, fun _ _ _ h => Gen.arbNatAux_monotonic h⟩

end IndexLawful
end Gen
