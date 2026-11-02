import properties.wasm_module_ok.ConstructiveTypeAtoms
import properties.wasm_module_not_ok.SubstOfResult

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveAliases
open properties.wasm_module_ok

/-- Traverse an existing type table to construct legal index alternatives.
The seed is a known representative. No AST candidate is built or validated. -/
def slots (target : SpecTec.deftype) (representative offset : Nat) :
    List SpecTec.deftype → Gen Nat
  | [] => pure representative
  | dt :: rest =>
      if dt = target then
        Gen.pick (pure offset) (slots target representative (offset + 1) rest)
      else slots target representative (offset + 1) rest

theorem slots_support (target : SpecTec.deftype) (representative offset : Nat)
    (table : List SpecTec.deftype) (x : Nat) :
    Gen.support (slots target representative offset table) x ↔
      x = representative ∨ ∃ i, table[i]? = some target ∧ x = offset + i := by
  induction table generalizing offset with
  | nil => simp [slots]
  | cons dt rest ih =>
    have hcons : (∃ i, (dt :: rest)[i]? = some target ∧ x = offset + i) ↔
        (dt = target ∧ x = offset) ∨
          ∃ i, rest[i]? = some target ∧ x = (offset + 1) + i := by
      constructor
      · rintro ⟨i, hi, hx⟩
        cases i with
        | zero => exact Or.inl ⟨by simpa using hi, by simpa using hx⟩
        | succ i => exact Or.inr ⟨i, by simpa using hi, by omega⟩
      · rintro (⟨hd, hx⟩ | ⟨i, hi, hx⟩)
        · exact ⟨0, by simpa using hd, by simpa using hx⟩
        · exact ⟨i + 1, by simpa using hi, by omega⟩
    rw [hcons]
    by_cases hd : dt = target
    · simp [slots, hd, ih, or_left_comm]
    · simp [slots, hd, ih]


/-- A known legal representative makes every traversal branch inhabited. -/
def aliases (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) : Gen Nat := slots target representative 0 table

theorem aliases_support (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) (hrep : table[representative]? = some target) (x : Nat) :
    Gen.support (aliases table target representative) x ↔ table[x]? = some target := by
  rw [aliases, slots_support]
  constructor
  · rintro (rfl | ⟨i, hi, hx⟩)
    · exact hrep
    · simpa [hx] using hi
  · intro hx
    exact Or.inr ⟨x, hx, by simp⟩

theorem slots_finite (target : SpecTec.deftype) (representative offset : Nat)
    (table : List SpecTec.deftype) :
    ConstructiveTypeAtoms.FiniteConstruction (slots target representative offset table) := by
  induction table generalizing offset with
  | nil => trivial
  | cons dt rest ih =>
    unfold slots
    split
    · exact ⟨trivial, ih _⟩
    · exact ih _

/-- Reify a closed definition to every original external static index. -/
def externalRefs (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) : Gen SpecTec.typevar :=
  SpecTec.typevar.StatX <$> aliases table target representative

theorem externalRefs_support (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) (hrep : table[representative]? = some target)
    (tv : SpecTec.typevar) :
    Gen.support (externalRefs table target representative) tv ↔
      properties.wasm_module_not_ok.Rejection.substOfResult tv table = some (.DefHT target) := by
  cases tv with
  | StatX x =>
    simp only [externalRefs, Gen.Support.support_map]
    constructor
    · rintro ⟨i, hi, he⟩
      cases he
      simp [properties.wasm_module_not_ok.Rejection.substOfResult,
        (aliases_support table target representative hrep x).1 hi]
    · intro h
      refine ⟨x, ?_, rfl⟩
      apply (aliases_support table target representative hrep x).2
      cases hx : table[x]? <;>
        simp_all [properties.wasm_module_not_ok.Rejection.substOfResult]
  | RecX x => simp [externalRefs, properties.wasm_module_not_ok.Rejection.substOfResult]

theorem externalRefs_finite (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) :
    properties.wasm_module_ok.ConstructiveTypeAtoms.FiniteConstruction
      (externalRefs table target representative) :=
  ⟨slots_finite _ _ _ _, fun _ => trivial⟩

theorem externalRefs_exact (table : List SpecTec.deftype) (target : SpecTec.deftype)
    (representative : Nat) (hrep : table[representative]? = some target)
    (tv : SpecTec.typevar) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype, SpecTec.SpecTecCall.«$subst_of» tv table⟩)
      start (.success (.of (.DefHT target : SpecTec.heaptype))) finish ↔
      Gen.support (externalRefs table target representative) tv ∧ finish = start := by
  rw [externalRefs_support table target representative hrep]
  constructor
  · intro h
    obtain ⟨hv, hn⟩ := properties.wasm_module_not_ok.Rejection.subst_of_deterministic_result
      tv table start finish _ h
    refine ⟨?_, hn⟩
    cases hr : properties.wasm_module_not_ok.Rejection.substOfResult tv table with
    | none => simp [properties.wasm_module_not_ok.Rejection.optionOutcome, hr] at hv
    | some ht =>
      simp only [hr, properties.wasm_module_not_ok.Rejection.optionOutcome,
        SpecTecExecution.Outcome.success.injEq, SpecTecExecution.Value.of.injEq] at hv
      exact congrArg some (eq_of_heq hv.2).symm
  · rintro ⟨hr, rfl⟩
    simpa only [hr, properties.wasm_module_not_ok.Rejection.optionOutcome] using
      properties.wasm_module_not_ok.Rejection.subst_of_total_result tv table finish

end properties.wasm_module_ok.ConstructiveAliases
