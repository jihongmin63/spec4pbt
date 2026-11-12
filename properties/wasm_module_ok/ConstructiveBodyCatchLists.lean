import properties.wasm_module_ok.ConstructiveBodyCatchOriginal
import properties.wasm_module_ok.ConstructiveBodyTryTable
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCatchLists
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyCatches ConstructiveBodyCatchCoverage ConstructiveConstTableCore

theorem list_support (c : context) (env : Env c) (xs : List (Handler c))
    (h : ∀x∈xs,x∈handlers c env) : Gen.support (lists c env).generator xs := by
  cases he : handlers c env with
  | nil =>
    have hx : xs=[] := by
      cases xs with
      | nil => rfl
      | cons x xs => have hh := h x (by simp); simp [he] at hh
    subst xs
    simp only [lists,he,Audited.pure]
    rfl
  | cons head tail =>
    simp only [lists,he]
    change Gen.support (ConstructiveLists.all
      (ConstructiveBodyChoice.branches (Audited.pure head) (tail.map Audited.pure)).generator) xs
    apply (ConstructiveLists.all_support _ xs).2
    intro x hx
    apply (ConstructiveBodyChoice.branches_support _ _ _).2
    have hm := h x hx
    rw [he] at hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨Audited.pure x,List.mem_cons_self,rfl⟩
    · exact ⟨Audited.pure x,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x,hm,rfl⟩),rfl⟩

theorem covered_list (c : context) (env : Env c) (xs : List SpecTec.«catch»)
    (h : ∀x∈xs,Covers c env x) :
    ∃ys : List (Handler c),ys.map Subtype.val=xs ∧ ∀y∈ys,y∈handlers c env := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨y,hy,he⟩ := h x (by simp)
    obtain ⟨ys,hys,hm⟩ := ih (fun z hz => h z (by simp [hz]))
    refine ⟨y::ys,by simp [he,hys],?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact hy
    · exact hm z hz

theorem iter_covered (c : context) (env : Env c) (outputs : List valtype)
    (xs : List SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.«Instr_ok:try_table:iter:0» c outputs xs⟩)
      start (.success (.of ())) finish) :
    (∀x∈xs,Covers c env x) ∧ finish=start := by
  induction xs generalizing start finish with
  | nil =>
    have hs := ConstructiveBodyTryTable.handlers_total c outputs [] start
    exact ⟨by simp,(properties.wasm_module_ok.Execution.eval_deterministic h hs).2⟩
  | cons x xs ih =>
    cases h with | call h =>
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«Instr_ok:try_table:iter:0_clauses» c outputs (x::xs)))
       start (.success (.of ())) finish at h
     cases h with
     | orElse_success h => cases h
     | orElse_unmatch hfailedSupply h =>
       restore_supply hfailedSupply at h
       cases h with
       | orElse_unmatch hfailedSupply h => restore_supply hfailedSupply at h; cases h
       | orElse_success h =>
         cases h with | bind_success hh h =>
          cases h with | bind_success ht hp =>
           cases hp
           obtain ⟨hc,hcounter⟩ := ConstructiveBodyCatchOriginal.original_complete c env outputs x _ _ hh
           obtain ⟨htc,htcounter⟩ := ih _ _ ht
           refine ⟨?_,htcounter.trans hcounter⟩
           intro y hy
           rcases List.mem_cons.mp hy with rfl|hy
           · exact hc
           · exact htc y hy

theorem lists_complete (c : context) (env : Env c) (outputs : List valtype)
    (xs : List SpecTec.«catch») (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.«Instr_ok:try_table:iter:0» c outputs xs⟩)
      start (.success (.of ())) finish) :
    ∃ys : List (Handler c),Gen.support (lists c env).generator ys ∧ ys.map Subtype.val=xs ∧ finish=start := by
  obtain ⟨hc,hf⟩ := iter_covered c env outputs xs start finish h
  obtain ⟨ys,he,hm⟩ := covered_list c env xs hc
  exact ⟨ys,list_support c env ys hm,he,hf⟩

#print axioms lists_complete
end properties.wasm_module_ok.ConstructiveBodyCatchLists
