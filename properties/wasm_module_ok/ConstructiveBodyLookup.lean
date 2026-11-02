import properties.wasm_module_ok.ConstructiveBodyProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyLookup

structure Entry {α : Type} (xs : List α) where
  index : Nat
  value : α
  lookup : xs[index]?=some value

def entries {α : Type} (xs : List α) : List (Entry xs) :=
  (List.finRange xs.length).map fun i => ⟨i.val,xs[i.val],List.getElem?_eq_getElem i.isLt⟩

theorem complete {α : Type} (xs : List α) (e : Entry xs) : e∈entries xs := by
  obtain ⟨hi,hv⟩ := List.getElem?_eq_some_iff.mp e.lookup
  apply List.mem_map.mpr
  refine ⟨⟨e.index,hi⟩,by simp,?_⟩
  cases e with | mk i v h =>
   simp only at hv
   congr 1

theorem Entry.mem {α : Type} {xs : List α} (e : Entry xs) : e.value∈xs :=
  List.mem_iff_getElem?.mpr ⟨e.index,e.lookup⟩

#print axioms complete
end properties.wasm_module_ok.ConstructiveBodyLookup
