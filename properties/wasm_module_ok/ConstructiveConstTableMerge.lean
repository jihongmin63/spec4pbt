import properties.wasm_module_ok.ConstructiveConstTableCore
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTableMerge
open SpecTec properties.wasm_module_ok ConstructiveConstTree
open ConstructiveConstBuilders ConstructiveConstTableCore

def Emits {c : context} (e : Entry c) (tree : Tree) : Prop :=
  ∃t,Gen.support e.values.generator t ∧ t.val=tree

def joined {c : context} (a b : Entry c) (he : b.type=a.type) : Entry c :=
  ⟨a.type,a.values.pick (b.values.map fun t => ⟨t.val,t.property.1,t.property.2.trans he⟩),a.inTable⟩

theorem joined_emits {c : context} (a b : Entry c) (he : b.type=a.type) (tree : Tree) :
    Emits (joined a b he) tree ↔ Emits a tree ∨ Emits b tree := by
  constructor
  · rintro ⟨t,ht,hv⟩
    rcases ht with ht|ht
    · exact Or.inl ⟨t,ht,hv⟩
    · obtain ⟨u,hu,heq⟩ := ht
      have huv : u.val=t.val := (congrArg Subtype.val heq).symm
      exact Or.inr ⟨u,hu,huv.trans hv⟩
  · rintro (⟨t,ht,hv⟩|⟨t,ht,hv⟩)
    · exact ⟨t,Or.inl ht,hv⟩
    · exact ⟨⟨t.val,t.property.1,t.property.2.trans he⟩,Or.inr ⟨t,ht,rfl⟩,hv⟩

/-- Equal output TYPE keys are merged by generator choice. No expression is
examined, rejected, or replaced; both generators remain in exact support. -/
def insert {c : context} (e : Entry c) : List (Entry c) → List (Entry c)
  | [] => [e]
  | h::t => if he : e.type=h.type then joined h e he::t else h::insert e t

def coalesce {c : context} : List (Entry c) → List (Entry c)
  | [] => []
  | e::es => insert e (coalesce es)

theorem insert_emits {c : context} (e : Entry c) (es : List (Entry c)) (tree : Tree) :
    (∃x∈insert e es,Emits x tree) ↔ Emits e tree ∨ ∃x∈es,Emits x tree := by
  induction es with
  | nil => simp [insert]
  | cons h t ih =>
    by_cases he : e.type=h.type
    · simp only [insert,dif_pos he,List.mem_cons,exists_eq_or_imp,joined_emits]
      tauto
    · simp only [insert,dif_neg he,List.mem_cons,exists_eq_or_imp,ih]
      tauto

theorem coalesce_emits {c : context} (es : List (Entry c)) (tree : Tree) :
    (∃x∈coalesce es,Emits x tree) ↔ ∃x∈es,Emits x tree := by
  induction es with
  | nil => simp [coalesce]
  | cons h t ih =>
    simp only [coalesce,insert_emits,ih,List.mem_cons,exists_eq_or_imp]

#print axioms coalesce_emits
end properties.wasm_module_ok.ConstructiveConstTableMerge
