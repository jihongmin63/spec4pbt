import properties.wasm_module_ok.FreeDeclarationValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeListValidation

open properties.wasm_module_ok.FreeUnionValidation

theorem free_list_cons_success_iff
    {X : Type} (f : X → SpecTec.Call SpecTec.free)
    (item : X) (rest : List X)
    (result : SpecTec.free) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» X f (item :: rest)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (headFree tailFree : SpecTec.free) (middle₁ middle₂ : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free, f item⟩)
        n (.success (.of headFree)) middle₁ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free,
          SpecTec.Call.«$free_list» X f rest⟩)
        middle₁ (.success (.of tailFree)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free,
          SpecTec.Call.«$fold_left» SpecTec.free SpecTec.free
            SpecTec.Call.«$free_union» headFree [tailFree]⟩)
        middle₂ (.success (.of result)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«$free_list:clause:0» X f (item :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«$free_list:clause:1» X f (item :: rest)]))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«$free_list:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«$free_list:clause:1» X f (item :: rest))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«$free_list:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle₁ headFree
                cases htail with
                | bind_success hrest htail =>
                  rename_i middle₂ tailFree
                  cases htail with
                  | bind_success hfold hpure =>
                    cases hpure with
                    | pure => exact ⟨headFree, tailFree,
                        middle₁, middle₂, hhead, hrest, hfold⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨headFree, tailFree, middle₁, middle₂,
      hhead, hrest, hfold⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$free_list_clauses» X f (item :: rest)))
      n (.success (.of result)) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$free_list:clause:0» X f (item :: rest)) n .unmatch n
      unfold SpecTec.«$free_list:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$free_list:clause:1» X f (item :: rest))
      n (.success (.of result)) finalSupply
    unfold SpecTec.«$free_list:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success hrest
    apply SpecTecExecution.Eval.bind_success hfold
    exact SpecTecExecution.Eval.pure _

theorem free_list_preserves_funcs
    {X : Type} (f : X → SpecTec.Call SpecTec.free)
    (P : X → Prop) (x : SpecTec.funcidx)
    (hitem : ∀ (item : X) (out : SpecTec.free)
      (start finalSupply : Nat), P item →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free, f item⟩)
        start (.success (.of out)) finalSupply → HasFunc out x)
    (xs : List X) (item : X) (hmem : item ∈ xs) (hP : P item)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_list» X f xs⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  induction xs generalizing n finalSupply result with
  | nil => cases hmem
  | cons head tail ih =>
      obtain ⟨headFree, tailFree, middle₁, middle₂,
        hhead, htail, hfold⟩ :=
        (free_list_cons_success_iff f head tail result n finalSupply).mp hcall
      obtain ⟨hresult, _⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic hfold
          (fold_left_singleton_total headFree tailFree middle₂)
      have hpart : HasFunc headFree x ∨ HasFunc tailFree x := by
        rcases List.mem_cons.mp hmem with h | h
        · exact .inl (hitem head headFree n middle₁ (h ▸ hP) hhead)
        · exact .inr (ih h tailFree middle₁ middle₂ htail)
      cases hresult
      exact hasFunc_union headFree tailFree x hpart

theorem free_globals_ref_func
    (gs : List SpecTec.global) (g : SpecTec.global)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (n finalSupply : Nat)
    (hg : g ∈ gs) (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» SpecTec.global
          SpecTec.Call.«$free_global» gs⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  exact free_list_preserves_funcs SpecTec.Call.«$free_global»
    (fun a : SpecTec.global => SpecTec.instr.«REF.FUNC» x ∈ a.GINIT) x
    (by intro item out start finish hm hc
        exact FreeDeclarationValidation.free_global_ref_func
          item x out start finish hm hc)
    gs g hg href result n finalSupply hcall

theorem free_tables_ref_func
    (ts : List SpecTec.table) (t : SpecTec.table)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (n finalSupply : Nat)
    (ht : t ∈ ts) (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» SpecTec.table
          SpecTec.Call.«$free_table» ts⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  exact free_list_preserves_funcs SpecTec.Call.«$free_table»
    (fun a : SpecTec.table => SpecTec.instr.«REF.FUNC» x ∈ a.TINIT) x
    (by intro item out start finish hm hc
        exact FreeDeclarationValidation.free_table_ref_func
          item x out start finish hm hc)
    ts t ht href result n finalSupply hcall

end properties.wasm_module_ok.FreeListValidation
