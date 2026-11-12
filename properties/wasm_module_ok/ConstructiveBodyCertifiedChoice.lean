import properties.wasm_module_ok.ConstructiveBodyChoice
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCertifiedChoice
open properties.wasm_module_ok ConstructiveConstTableCore

/-- Every alternative is certified before choice. No test or discarded branch. -/
def choose {α : Type} {P : α → Prop} (head : α) (tail : List α)
    (all : ∀a∈head::tail,P a) : Audited {a // P a} :=
  ConstructiveBodyChoice.branches (Audited.pure ⟨head,all head List.mem_cons_self⟩)
    (tail.attach.map fun a => Audited.pure ⟨a.val,all a.val (List.mem_cons_of_mem _ a.property)⟩)

theorem complete {α : Type} {P : α → Prop} (head : α) (tail : List α)
    (all : ∀a∈head::tail,P a) (a : {a // P a}) (h : a.val∈head::tail) :
    Gen.support (choose head tail all).generator a := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  rcases List.mem_cons.mp h with he|hm
  · have ha : a=⟨head,all head List.mem_cons_self⟩ := Subtype.ext he
    subst a
    exact ⟨_,List.mem_cons_self,rfl⟩
  · refine ⟨Audited.pure a,List.mem_cons_of_mem _ ?_,rfl⟩
    apply List.mem_map.mpr
    refine ⟨⟨a.val,hm⟩,List.mem_attach _ _,?_⟩
    rfl

theorem exact_support {α : Type} {P : α → Prop} (head : α) (tail : List α)
    (all : ∀a∈head::tail,P a) (a : {a // P a}) :
    Gen.support (choose head tail all).generator a ↔ a.val∈head::tail := by
  constructor
  · intro h
    obtain ⟨g,hg,hs⟩ := (ConstructiveBodyChoice.branches_support _ _ _).1 h
    rcases List.mem_cons.mp hg with he|hm
    · subst g; change a= _ at hs; cases hs; exact List.mem_cons_self
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
      subst g
      change a= _ at hs; cases hs
      exact List.mem_cons_of_mem _ v.property
  · exact complete head tail all a

#print axioms exact_support
end properties.wasm_module_ok.ConstructiveBodyCertifiedChoice
