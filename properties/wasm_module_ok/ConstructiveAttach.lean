import properties.wasm_module_ok.ConstructiveGenAudit

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveAttach
open properties.wasm_module_ok

def Monotone {α : Type} (f : Nat → Gen (Option α)) : Prop :=
  ∀ a n k, Gen.support (f n) (some a) → Gen.support (f (n+k)) (some a)

def optionWitness {α : Type} (f : Nat → Gen (Option α)) (hm : Monotone f) (n : Nat) :
    {o : Option α // Gen.support (f n) o} → Option {a : α // Gen.support (Gen.indexed f) a}
  | ⟨none,_⟩ => none
  | ⟨some a,ha⟩ => some ⟨a,hm,n,ha⟩

/-- Retain the branch's already established support proof as erased data.
This traverses the generator syntax; it never tests or replaces an output.
An indexed node is accepted only with its recursive monotonicity audit. -/
def attach {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g) :
    Gen {a : α // Gen.support g a} :=
  match g with
  | .ret a => pure ⟨a,rfl⟩
  | .pick a b => Gen.pick
      ((fun x => ⟨x.val,Or.inl x.property⟩) <$> attach a h.1)
      ((fun x => ⟨x.val,Or.inr x.property⟩) <$> attach b h.2)
  | .bind a k => do
      let x ← attach a h.1
      let y ← attach (k x.val) (h.2 x.val)
      pure ⟨y.val,x.val,x.property,y.property⟩
  | .assume _ _ => False.elim h
  | .indexed f => Gen.indexed (fun n => optionWitness f h.2 n <$> attach (f n) (h.1 n))

theorem option_support {α : Type} (f : Nat → Gen (Option α)) (hm : Monotone f) (n : Nat)
    (g : Gen {o : Option α // Gen.support (f n) o})
    (hg : ∀ o ho, Gen.support g ⟨o,ho⟩)
    (a : {v : α // Gen.support (Gen.indexed f) v}) :
    Gen.support (optionWitness f hm n <$> g) (some a) ↔ Gen.support (f n) (some a.val) := by
  rw [Gen.Support.support_map]
  constructor
  · rintro ⟨⟨o,ho⟩,_,heq⟩
    cases o with
    | none => cases heq
    | some v =>
      have he : a.val = v := congrArg Subtype.val (Option.some.inj heq)
      simpa only [he] using ho
  · intro ha
    exact ⟨⟨some a.val,ha⟩,hg _ _,rfl⟩

theorem cover {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g)
    (a : α) (ha : Gen.support g a) : Gen.support (attach g h) ⟨a,ha⟩ := by
  induction g with
  | ret v =>
    have he : a = v := ha
    subst a
    rfl
  | pick x y ihx ihy =>
    rcases ha with ha | ha
    · apply Or.inl
      exact ⟨⟨a,ha⟩,ihx h.1 a ha,rfl⟩
    · apply Or.inr
      exact ⟨⟨a,ha⟩,ihy h.2 a ha,rfl⟩
  | bind x k ihx ihk =>
    obtain ⟨v,hv,ha⟩ := ha
    exact ⟨⟨v,hv⟩,ihx h.1 v hv,⟨a,ha⟩,ihk v (h.2 v) a ha,rfl⟩
  | assume b k ih => exact False.elim h
  | indexed f ih =>
    have hf : ∀ n (v : {a : _ // Gen.support (Gen.indexed f) a}),
        Gen.support (optionWitness f h.2 n <$> attach (f n) (h.1 n)) (some v) ↔
          Gen.support (f n) (some v.val) := by
      intro n v
      exact option_support f h.2 n _ (fun o ho => ih n (h.1 n) o ho) v
    constructor
    · intro v n k hn
      exact (hf (n+k) v).2 (h.2 v.val n k ((hf n v).1 hn))
    · obtain ⟨n,hn⟩ := ha.2
      exact ⟨n,(hf n ⟨a,ha⟩).2 hn⟩

theorem audit {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g) :
    ConstructiveGenAudit.Structural (attach g h) := by
  induction g with
  | ret a => trivial
  | pick x y ihx ihy => exact ⟨⟨ihx h.1,fun _ => trivial⟩,⟨ihy h.2,fun _ => trivial⟩⟩
  | bind x k ihx ihk =>
    exact ⟨ihx h.1,fun v => ⟨ihk v.val (h.2 v.val),fun _ => trivial⟩⟩
  | assume b k ih => exact False.elim h
  | indexed f ih =>
    constructor
    · intro n
      exact ⟨ih n (h.1 n),fun _ => trivial⟩
    · intro v n k hn
      have hf := fun n v => option_support f h.2 n (attach (f n) (h.1 n))
        (cover (f n) (h.1 n)) v
      exact (hf (n+k) v).2 (h.2 v.val n k ((hf n v).1 hn))

def refine {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g)
    (P : α → Prop) (hp : ∀ a, Gen.support g a → P a) : Gen {a : α // P a} :=
  (fun a => ⟨a.val,hp a.val a.property⟩) <$> attach g h

theorem refine_support {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g)
    (P : α → Prop) (hp : ∀ a, Gen.support g a → P a) (a : {a : α // P a}) :
    Gen.support (refine g h P hp) a ↔ Gen.support g a.val := by
  rw [refine, Gen.Support.support_map]
  constructor
  · rintro ⟨b,_,rfl⟩
    exact b.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,cover g h a.val ha,rfl⟩

theorem refine_audit {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g)
    (P : α → Prop) (hp : ∀ a, Gen.support g a → P a) :
    ConstructiveGenAudit.Structural (refine g h P hp) := ⟨audit g h,fun _ => trivial⟩

end properties.wasm_module_ok.ConstructiveAttach
