import properties.wasm_module_ok.ConstructiveAliases
import properties.wasm_module_not_ok.HeaptypeRollValidation
import properties.wasm_module_not_ok.HeaptypeSubstOfValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveRelocateIndices
open SpecTec
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection

/-- Reify a source index from an earlier group at the current table end.
Internal references are shifted exactly; external references choose all aliases.
The finite source bound makes every branch productive without a failed lookup. -/
def relocate (table : List deftype) (oldBase width : Nat)
    (hle : oldBase ≤ table.length) (i : Fin (oldBase + width)) : Gen Nat :=
  if hlocal : oldBase ≤ i.val then
    pure (table.length + (i.val - oldBase))
  else
    ConstructiveAliases.aliases table (table[i.val]'(by omega)) i.val

/-- The exact original roll-then-substitute leaf transformation. -/
def closedIndex (table : List deftype) (base width index : Nat) : Option heaptype :=
  substHeaptypeResult (rollTypevar (.StatX index) base (base + width)) table

@[simp] theorem closedIndex_local (table : List deftype) (base width index : Nat)
    (h : base ≤ index ∧ index < base + width) :
    closedIndex table base width index = some (.VarHT (.RecX (index - base))) := by
  simp [closedIndex, rollTypevar, h, substHeaptypeResult, substOfResult]

@[simp] theorem closedIndex_external (table : List deftype) (base width index : Nat)
    (h : index < base) :
    closedIndex table base width index = (table[index]?).map heaptype.DefHT := by
  have hh : ¬(base ≤ index ∧ index < base+width) := by omega
  simp [closedIndex, rollTypevar, hh, substHeaptypeResult, substOfResult]

theorem relocate_finite (table : List deftype) (oldBase width : Nat)
    (hle : oldBase ≤ table.length) (i : Fin (oldBase + width)) :
    ConstructiveTypeAtoms.FiniteConstruction (relocate table oldBase width hle i) := by
  unfold relocate
  split
  · trivial
  · exact ConstructiveAliases.slots_finite _ _ _ _

/-- Every raw index with the same closed leaf is retained, including source
aliases. Bounds and the two disjoint constructors prove total productivity. -/
theorem relocate_support (table : List deftype) (oldBase width : Nat)
    (hle : oldBase ≤ table.length) (i : Fin (oldBase + width)) (j : Nat) :
    Gen.support (relocate table oldBase width hle i) j ↔
      j < table.length + width ∧
      closedIndex table table.length width j = closedIndex table oldBase width i.val := by
  by_cases hl : oldBase ≤ i.val
  · have hi : i.val < oldBase + width := i.isLt
    rw [relocate, dif_pos hl, Gen.Support.support_pure]
    rw [closedIndex_local table oldBase width i.val ⟨hl, hi⟩]
    constructor
    · intro hj
      subst j
      have hb : table.length ≤ table.length + (i.val-oldBase) ∧
          table.length + (i.val-oldBase) < table.length+width := by omega
      refine ⟨hb.2, ?_⟩
      simp [closedIndex_local table _ _ _ hb]
    · rintro ⟨hj, he⟩
      by_cases hnew : table.length ≤ j
      · rw [closedIndex_local table _ _ _ ⟨hnew,hj⟩] at he
        simp only [Option.some.injEq, heaptype.VarHT.injEq, typevar.RecX.injEq] at he
        omega
      · have hjold : j < table.length := by omega
        rw [closedIndex_external table _ _ _ hjold] at he
        cases hx : table[j]? <;> simp [hx] at he
  · have hi : i.val < oldBase := by omega
    have hit : i.val < table.length := by omega
    have hrep : table[i.val]? = some (table[i.val]'hit) := List.getElem?_eq_getElem hit
    rw [relocate, dif_neg hl,
      ConstructiveAliases.aliases_support table (table[i.val]'hit) i.val hrep j]
    rw [closedIndex_external table oldBase width i.val hi, hrep]
    simp only [Option.map_some]
    constructor
    · intro hj
      have hjb : j < table.length := (List.getElem?_eq_some_iff.mp hj).1
      refine ⟨by omega, ?_⟩
      rw [closedIndex_external table _ _ _ hjb, hj]
      rfl
    · rintro ⟨hj, he⟩
      by_cases hnew : table.length ≤ j
      · rw [closedIndex_local table _ _ _ ⟨hnew,hj⟩] at he
        cases he
      · have hjold : j < table.length := by omega
        rw [closedIndex_external table _ _ _ hjold] at he
        cases hx : table[j]? with
        | none => simp [hx] at he
        | some dt =>
          simp only [hx, Option.map_some, Option.some.injEq, heaptype.DefHT.injEq] at he
          simpa [he] using hx

#print axioms relocate_support
end properties.wasm_module_ok.ConstructiveRelocateIndices
