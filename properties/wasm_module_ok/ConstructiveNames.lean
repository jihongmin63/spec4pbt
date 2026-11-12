import properties.wasm_module_ok.ConstructiveGenAudit
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Sort
import Palamedes.Data.Nat

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveNames

def encode : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.pair x (encode xs) + 1

def decode : Nat → List Nat
  | 0 => []
  | n + 1 => (Nat.unpair n).1 :: decode (Nat.unpair n).2
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

@[simp] theorem decode_encode (xs : List Nat) : decode (encode xs) = xs := by
  induction xs with
  | nil => simp [encode, decode]
  | cons x xs ih => simp [encode, decode, ih]

@[simp] theorem encode_decode (n : Nat) : encode (decode n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [encode, decode]
    | succ k =>
      simp only [decode, encode]
      rw [ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le k)), Nat.pair_unpair]

theorem encode_injective : Function.Injective encode := by
  intro a b h
  simpa using congrArg decode h

/-- Interpret a rank among the allowed numbers. Each forbidden boundary shifts
the remaining rank; no candidate is validated, discarded, or replaced. -/
def unrank : List Nat → Nat → Nat
  | [] => id
  | b :: bs => fun n => if n < b then n else unrank bs (n + 1)

theorem unrank_ge (bs : List Nat) (n : Nat) : n ≤ unrank bs n := by
  induction bs generalizing n with
  | nil => exact Nat.le_refl n
  | cons b bs ih =>
    simp only [unrank]
    split
    · exact Nat.le_refl n
    · exact Nat.le_trans (Nat.le_succ n) (ih (n + 1))

theorem unrank_below (bs : List Nat) (n : Nat)
    (h : ∀ b ∈ bs, n < b) : unrank bs n = n := by
  cases bs with
  | nil => rfl
  | cons b bs => simp [unrank, h b (by simp)]

theorem unrank_not_mem (bs : List Nat) (hs : bs.Pairwise (· < ·)) (n : Nat) :
    unrank bs n ∉ bs := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hs
    by_cases hn : n < b
    · simp only [unrank, if_pos hn, List.mem_cons, not_or]
      refine ⟨by omega, ?_⟩
      intro hm
      have := hb n hm
      omega
    · simp only [unrank, if_neg hn, List.mem_cons, not_or]
      refine ⟨?_, ih hbs (n + 1)⟩
      have := unrank_ge bs (n + 1)
      omega

theorem unrank_surjective (bs : List Nat) (hs : bs.Pairwise (· < ·))
    (x : Nat) (hx : x ∉ bs) : ∃ n, unrank bs n = x := by
  induction bs generalizing x with
  | nil => exact ⟨x, rfl⟩
  | cons b bs ih =>
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hs
    have hxb : x ≠ b := fun h => hx (by simp [h])
    have hxbs : x ∉ bs := fun h => hx (List.mem_cons_of_mem b h)
    by_cases hlt : x < b
    · exact ⟨x, by simp [unrank, hlt]⟩
    · obtain ⟨n, hn⟩ := ih hbs x hxbs
      have hbn : b < n := by
        by_contra h
        have heq : unrank bs n = n := unrank_below bs n (by
          intro y hy
          have := hb y hy
          omega)
        omega
      refine ⟨n - 1, ?_⟩
      have hnlt : ¬ n - 1 < b := by omega
      have hnpos : n - 1 + 1 = n := by omega
      simp [unrank, hnlt, hnpos, hn]

def forbidden (used : List SpecTec.name) : List Nat :=
  ((used.map encode).toFinset).sort

@[simp] theorem mem_forbidden (used : List SpecTec.name) (name : SpecTec.name) :
    encode name ∈ forbidden used ↔ name ∈ used := by
  simp only [forbidden, Finset.mem_sort, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact encode_injective heq ▸ hx
  · intro h
    exact ⟨name, h, rfl⟩

theorem forbidden_sorted (used : List SpecTec.name) :
    (forbidden used).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

def fresh (used : List SpecTec.name) : Gen SpecTec.name :=
  (fun n => decode (unrank (forbidden used) n)) <$> Gen.arbNat

theorem fresh_exact (used : List SpecTec.name) (name : SpecTec.name) :
    Gen.support (fresh used) name ↔ name ∉ used := by
  simp only [fresh, Gen.Support.support_map, Gen.support_arbNat, true_and]
  constructor
  · rintro ⟨n, rfl⟩ h
    have := (mem_forbidden used (decode (unrank (forbidden used) n))).2 h
    rw [encode_decode] at this
    exact unrank_not_mem _ (forbidden_sorted used) n this
  · intro h
    obtain ⟨n, hn⟩ := unrank_surjective _ (forbidden_sorted used) (encode name)
      (by simpa using h)
    exact ⟨n, by rw [hn, decode_encode]⟩


theorem fresh_audit (used : List SpecTec.name) :
    ConstructiveGenAudit.Structural (fresh used) := by
  simp [fresh]

theorem fresh_total (used : List SpecTec.name) : Gen.total (fresh used) :=
  ConstructiveGenAudit.audit_total _ (fresh_audit used)

end properties.wasm_module_ok.ConstructiveNames
