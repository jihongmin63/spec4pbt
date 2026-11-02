import properties.wasm_module_ok.ValtypeValidation
import properties.wasm_module_ok.ReftypeTotal
import Spec4Pbt.CorrectGen

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeAtoms
open SpecTec SpecTecExecution
open properties.wasm_module_ok

/-- Nonempty finite choice, with no failure or indexed nodes. -/
def choose {α : Type} (head : α) : List α → Gen α
  | [] => pure head
  | x :: xs => Gen.pick (pure head) (choose x xs)

@[simp] theorem support_choose {α : Type} (head : α) (tail : List α) (x : α) :
    Gen.support (choose head tail) x ↔ x ∈ head :: tail := by
  induction tail generalizing head with
  | nil => simp [choose]
  | cons a xs ih => simp [choose, ih]

/-- All branches are literal base types or indices constructed inside the bound. -/
def heaptypes (c : context) : Gen heaptype :=
  choose .AnyHT ([.NoneHT, .EqHT, .I31HT, .StructHT, .ArrayHT,
    .FuncHT, .NoFuncHT, .ExnHT, .NoExnHT, .ExternHT, .NoExternHT, .BotHT] ++
    (List.range c.TYPES.length).map (fun x => heaptype.VarHT (.StatX x)))

@[simp] theorem support_heaptypes (c : context) (t : heaptype) :
    Gen.support (heaptypes c) t ↔ HeaptypeValidation.heaptypeValid c t = true := by
  rw [HeaptypeValidation.heaptype_valid_iff]
  simp only [heaptypes, support_choose, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_range]
  simp only [HeaptypeValidation.baseHeaptypes, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · obtain ⟨x, hx, ht⟩ := h
      exact Or.inr ⟨x, ht.symm, hx⟩
  · rintro (h | ⟨x, ht, hx⟩)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, hx, ht.symm⟩)

theorem heaptypes_exact (c : context) (t : heaptype) (n fin : Nat) :
    Eval specTecProgram (.call ⟨Unit, SpecTecCall.Heaptype_ok c t⟩)
      n (.success (.of ())) fin ↔ Gen.support (heaptypes c) t ∧ fin = n := by
  rw [HeaptypeValidation.heaptype_success_iff_valid, support_heaptypes]

def reftypes (c : context) : Gen reftype := do
  let ht ← heaptypes c
  Gen.pick (pure (.«% %» .Null ht)) (pure (.«% %» .NoNull ht))

@[simp] theorem support_reftypes (c : context) (t : reftype) :
    Gen.support (reftypes c) t ↔ ReftypeTotal.reftypeValid c t = true := by
  cases t with
  | «% %» nullable ht =>
    cases nullable <;>
      simp [reftypes, ReftypeTotal.reftypeValid, support_heaptypes]

theorem reftypes_exact (c : context) (t : reftype) (n fin : Nat) :
    Eval specTecProgram (.call ⟨Unit, SpecTecCall.Reftype_ok c t⟩)
      n (.success (.of ())) fin ↔ Gen.support (reftypes c) t ∧ fin = n := by
  rw [ReftypeTotal.reftype_success_iff_valid, support_reftypes]

def valtypes (c : context) : Gen valtype :=
  Gen.pick
    (choose (.NumT .I32T) [.NumT .I64T, .NumT .F32T, .NumT .F64T, .VecT .V128T])
    (valtype.RefT <$> reftypes c)

@[simp] theorem support_valtypes (c : context) (t : valtype) :
    Gen.support (valtypes c) t ↔ ValtypeValidation.valtypeValid c t = true := by
  cases t with
  | NumT nt => cases nt <;> simp [valtypes, ValtypeValidation.valtypeValid]
  | VecT vt => cases vt; simp [valtypes, ValtypeValidation.valtypeValid]
  | RefT rt =>
    cases rt; simp [valtypes, ValtypeValidation.valtypeValid, ReftypeTotal.reftypeValid]
  | BotT => simp [valtypes, ValtypeValidation.valtypeValid]

theorem valtypes_exact (c : context) (t : valtype) (n fin : Nat) :
    Eval specTecProgram (.call ⟨Unit, SpecTecCall.Valtype_ok c t⟩)
      n (.success (.of ())) fin ↔ Gen.support (valtypes c) t ∧ fin = n := by
  rw [ValtypeValidation.valtype_success_iff_valid, support_valtypes]

/-- Structural part of the audit: no assume, indexed, or empty alternative.
Host-language functions still require source review for hidden screening. -/
def FiniteConstruction {α : Type} : Gen α → Prop
  | .ret _ => True
  | .pick a b => FiniteConstruction a ∧ FiniteConstruction b
  | .bind a k => FiniteConstruction a ∧ ∀ x, FiniteConstruction (k x)
  | .assume _ _ => False
  | .indexed _ => False

@[simp] theorem finite_choose {α : Type} (h : α) (t : List α) :
    FiniteConstruction (choose h t) := by
  induction t generalizing h with
  | nil => trivial
  | cons a xs ih => exact ⟨trivial, ih a⟩

theorem heaptypes_finite (c : context) : FiniteConstruction (heaptypes c) :=
  finite_choose _ _

theorem reftypes_finite (c : context) : FiniteConstruction (reftypes c) :=
  ⟨heaptypes_finite c, fun _ => ⟨trivial, trivial⟩⟩

theorem valtypes_finite (c : context) : FiniteConstruction (valtypes c) :=
  ⟨finite_choose _ _, reftypes_finite c, fun _ => trivial⟩

theorem finite_total {α : Type} (g : Gen α) (h : FiniteConstruction g) : Gen.total g := by
  induction g with
  | ret a => exact Gen.Total.total_pure
  | pick a b ia ib => exact Gen.Total.total_pick (ia h.1) (ib h.2)
  | bind a k ia ik =>
    apply Gen.Total.total_bind (ia h.1)
    intro x _
    exact ik x (h.2 x)
  | assume b k ih => exact h.elim
  | indexed f ih => exact h.elim


end properties.wasm_module_ok.ConstructiveTypeAtoms
