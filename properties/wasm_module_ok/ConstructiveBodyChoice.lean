import properties.wasm_module_ok.ConstructiveLimits
import properties.wasm_module_ok.ConstructiveAttach
import properties.wasm_module_ok.ConstructiveConstTableCore
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyChoice
open properties.wasm_module_ok ConstructiveConstTableCore

def index (bound : Nat) : Audited (Fin (bound+1)) :=
  let audited := ConstructiveGenAudit.finite_audit _ (ConstructiveLimits.bounded_finite bound)
  let g := ConstructiveAttach.refine (ConstructiveLimits.bounded bound) audited
    (fun v => v≤bound) (fun v hv => (ConstructiveLimits.bounded_support bound v).1 hv)
  (⟨g,ConstructiveAttach.refine_audit _ audited _ _⟩ : Audited {v : Nat // v≤bound}).map
    fun v => ⟨v.val,by omega⟩

theorem index_support (bound : Nat) (i : Fin (bound+1)) :
    Gen.support (index bound).generator i := by
  let audited := ConstructiveGenAudit.finite_audit _ (ConstructiveLimits.bounded_finite bound)
  have hi : i.val≤bound := by omega
  refine ⟨⟨i.val,hi⟩,?_,rfl⟩
  exact (ConstructiveAttach.refine_support (ConstructiveLimits.bounded bound) audited
    (fun v => v≤bound) (fun v hv => (ConstructiveLimits.bounded_support bound v).1 hv) ⟨i.val,hi⟩).2
      ((ConstructiveLimits.bounded_support bound i.val).2 hi)

/-- Balanced branch choice uses a constructed valid index. It never selects
or tests an AST candidate; each branch already constructs successful outputs. -/
def branches {α : Type} (head : Audited α) (tail : List (Audited α)) : Audited α :=
  (index tail.length).bind fun i => (head::tail)[i.val]

theorem branches_support {α : Type} (head : Audited α) (tail : List (Audited α)) (a : α) :
    Gen.support (branches head tail).generator a ↔ ∃g∈head::tail,Gen.support g.generator a := by
  constructor
  · rintro ⟨i,_,ha⟩
    exact ⟨_,List.getElem_mem _,ha⟩
  · rintro ⟨g,hg,ha⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hg
    exact ⟨⟨i,by simpa using hi⟩,index_support _ _,by simpa [he] using ha⟩

#print axioms branches_support
end properties.wasm_module_ok.ConstructiveBodyChoice
