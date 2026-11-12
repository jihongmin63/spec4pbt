import properties.wasm_module_ok.ConstructiveRelocateIndices
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyOrder
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveRelocateIndices
/-- Earlier parent positions remain earlier even when an external reference
chooses any existing alias. No alias is discarded to enforce this bound. -/
theorem relocate_before (table : List deftype) (base width pos : Nat)
    (hle : base≤table.length) (i : Fin (base+width)) (j : Nat)
    (hi : i.val<base+pos) (hg : Gen.support (relocate table base width hle i) j) :
    j<table.length+pos := by
  unfold relocate at hg
  split at hg
  next hl =>
    simp only [Gen.Support.support_pure] at hg
    omega
  next hl =>
    have hit : i.val<table.length := by omega
    have hj := (ConstructiveAliases.aliases_support table (table[i.val]'hit) i.val
      (List.getElem?_eq_getElem hit) j).1 hg
    have hjb := (List.getElem?_eq_some_iff.1 hj).1
    omega
#print axioms relocate_before
end properties.wasm_module_ok.ConstructiveTypeCopyOrder
