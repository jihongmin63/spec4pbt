import properties.wasm_module_ok.ConstructiveLimits
import properties.wasm_module_ok.ConstructiveAttach
import properties.wasm_module_ok.ConstructiveLists
import Init.Data.Char.Ordinal
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleStrings
open properties.wasm_module_ok

def ordinals : Gen (Fin Char.numCodePoints) :=
  (fun n : {n : Nat // n≤Char.numCodePoints-1} => (⟨n.val,Nat.lt_of_le_of_lt n.property (by decide)⟩ : Fin Char.numCodePoints)) <$>
    ConstructiveAttach.refine (ConstructiveLimits.bounded (Char.numCodePoints-1))
      (ConstructiveGenAudit.finite_audit _ (ConstructiveLimits.bounded_finite _)) _
      (fun n hn => (ConstructiveLimits.bounded_support _ n).1 hn)

theorem ordinals_complete (i : Fin Char.numCodePoints) : Gen.support ordinals i := by
  refine ⟨⟨i.val,Nat.le_pred_of_lt i.isLt⟩,?_,rfl⟩
  rw [ConstructiveAttach.refine_support,ConstructiveLimits.bounded_support]
  change i.val≤Char.numCodePoints-1
  exact Nat.le_pred_of_lt i.isLt

def chars : Gen Char := Char.ofOrdinal <$> ordinals
def strings : Gen String := String.ofList <$> ConstructiveLists.all chars

theorem chars_complete (c : Char) : Gen.support chars c :=
  ⟨c.ordinal,ordinals_complete c.ordinal,Char.ofOrdinal_ordinal.symm⟩
theorem strings_complete (s : String) : Gen.support strings s := by
  refine ⟨s.toList,?_,by simp⟩
  rw [ConstructiveLists.all_support]
  exact fun c _ => chars_complete c

theorem strings_audit : ConstructiveGenAudit.Structural strings := by
  apply (ConstructiveGenAudit.map_audit _ _).2
  apply ConstructiveLists.all_audit
  apply (ConstructiveGenAudit.map_audit _ _).2
  apply (ConstructiveGenAudit.map_audit _ _).2
  exact ConstructiveAttach.refine_audit _ _ _ _
#print axioms strings_complete
end properties.wasm_module_ok.ConstructiveModuleStrings
