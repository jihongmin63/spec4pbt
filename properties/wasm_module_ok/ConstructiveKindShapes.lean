import properties.wasm_module_ok.ConstructiveVarianceShapes
import properties.wasm_module_ok.ConstructiveAttach

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveKindShapes
open SpecTec properties.wasm_module_ok
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace ConstructiveVarianceShapes

/-- The skeleton chooses a structural kind first. Root signatures then cover
the entire raw domain of that kind, with unbounded finite list lengths. -/
def ofKind (c : context) (k : Kind) : Gen strtype :=
  match k with
  | .structK => strtype.DefStructT <$> ConstructiveTypeShapes.structs c
  | .arrayK => strtype.DefArrayT <$> ConstructiveTypeShapes.arrays c
  | .funcK => strtype.DefFuncT <$> ConstructiveTypeShapes.functions c

theorem ofKind_support (c : context) (k : Kind) (s : strtype) :
    Gen.support (ofKind c k) s ↔ ValidShape c.TYPES.length s ∧ kind s = k := by
  rw [valid_shape_iff]
  cases k <;> cases s <;> simp [ofKind, kind, StrtypeValidation.strtypeValid]

theorem ofKind_audit (c : context) (k : Kind) : ConstructiveGenAudit.Structural (ofKind c k) := by
  cases k <;> rw [ofKind, ConstructiveGenAudit.map_audit]
  · exact ConstructiveTypeShapes.structs_audit c
  · exact ConstructiveTypeShapes.arrays_audit c
  · exact ConstructiveTypeShapes.functions_audit c

def root (c : context) (k : Kind) : Gen {s : strtype // ValidShape c.TYPES.length s ∧ kind s = k} :=
  ConstructiveAttach.refine (ofKind c k) (ofKind_audit c k) _
    (fun s hs => (ofKind_support c k s).1 hs)

theorem root_covers (c : context) (k : Kind)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = k}) :
    Gen.support (root c k) s := by
  rw [root, ConstructiveAttach.refine_support, ofKind_support]
  exact s.property

theorem root_audit (c : context) (k : Kind) : ConstructiveGenAudit.Structural (root c k) :=
  ConstructiveAttach.refine_audit _ _ _ _

theorem match_kind (r : heaptype → heaptype → Bool) (a b : strtype)
    (h : MatchStrtypeConditional.strMatch r a b = true) : kind a = kind b := by
  cases a <;> cases b <;> simp_all [MatchStrtypeConditional.strMatch, kind]

theorem below_kind (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (target : strtype) (ht : ValidShape c.TYPES.length target) (out : strtype)
    (hout : Gen.support (below c r target ht) out) : kind out = kind target :=
  match_kind r out target ((below_support c r hr target ht out).1 hout).2

def child (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (target : strtype) (ht : ValidShape c.TYPES.length target) :
    Gen {s : strtype // ValidShape c.TYPES.length s ∧ kind s = kind target} :=
  ConstructiveAttach.refine (below c r target ht) (below_audit c r target ht) _
    (fun s hs => ⟨((below_support c r hr target ht s).1 hs).1,
      below_kind c r hr target ht s hs⟩)

theorem child_support (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (target : strtype) (ht : ValidShape c.TYPES.length target)
    (s : {s : strtype // ValidShape c.TYPES.length s ∧ kind s = kind target}) :
    Gen.support (child c r hr target ht) s ↔ MatchStrtypeConditional.strMatch r s.val target = true := by
  rw [child, ConstructiveAttach.refine_support, below_support c r hr target ht]
  exact and_iff_right s.property.1

theorem child_audit (c : context) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, ConstructiveTypeCopy.HeapBound c.TYPES.length h → r h h = true)
    (target : strtype) (ht : ValidShape c.TYPES.length target) :
    ConstructiveGenAudit.Structural (child c r hr target ht) :=
  ConstructiveAttach.refine_audit _ _ _ _

end properties.wasm_module_ok.ConstructiveKindShapes
