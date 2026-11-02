import properties.wasm_module_ok.ConstructiveBodyMemoryChoices
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryImmediates
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore ConstructiveBodyMemoryChoices ConstructiveBodyMemoryOperands

abbrev Immediate (addr : addrtype) (width : Nat) :=
  {value : Nat × Nat // value.1≤width ∧ OffsetBound addr value.2}

def generate (addr : addrtype) (width : Nat) : Audited (Immediate addr width) :=
  (ConstructiveBodyChoice.index width).bind fun align =>
    (offsets addr).map fun offset => ⟨(align.val,offset.val),⟨by omega,offset.property⟩⟩

theorem complete (addr : addrtype) (width : Nat) (v : Immediate addr width) :
    Gen.support (generate addr width).generator v := by
  refine ⟨⟨v.val.1,by have h:=v.property.1; omega⟩,ConstructiveBodyChoice.index_support _ _,?_⟩
  refine ⟨⟨v.val.2,v.property.2⟩,offsets_complete _ _,?_⟩
  apply Subtype.ext
  exact Prod.eta _

#print axioms complete
end properties.wasm_module_ok.ConstructiveBodyMemoryImmediates
