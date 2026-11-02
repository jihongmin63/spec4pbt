import properties.wasm_module_ok.ConstructiveModuleRefsBounds
import properties.wasm_module_ok.ConstructivePreludeRefs
import properties.wasm_module_ok.DeclarationConstValidation
import properties.wasm_module_ok.TablesDecision
import properties.wasm_module_ok.GlobalsDecision
import properties.wasm_module_ok.CandidateProvenanceGlobals
import properties.wasm_module_ok.CandidateProvenancePreGlobals
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleInitializerRefs
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs

abbrev Available (refs : SpecTec.free) (xs : List instr) :=
  ∀x,instr.«REF.FUNC» x∈xs → FreeUnionValidation.HasFunc refs x

theorem table_replace (refs : SpecTec.free) (c out : context) (item : SpecTec.table) (n finish : Nat)
    (ha : Available refs item.TINIT)
    (h : Eval Body (.call ⟨context,Call.Table_ok c item⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Table_ok (replace refs c) item⟩)
      n (.success (.of (replace refs out))) finish := by
  rcases item with ⟨⟨addr,lim,rt⟩,code⟩
  cases h with | call h =>
    change Eval Body (.orElse (SpecTec.«Table_ok:clause:0» c _) (fun _ => .unmatch)) n _ finish at h
    cases h with
    | orElse_success h =>
      unfold SpecTec.«Table_ok:clause:0» at h
      cases h with | bind_success htype h =>
        rename_i n1 unit
        cases unit
        cases h with | bind_success hc hp =>
          cases hp
          have ht := (TabletypeValidation.tabletype_success_iff_valid c (.TableT addr lim rt) n n1).1 htype
          have ht' := (TabletypeValidation.tabletype_success_iff_valid (replace refs c) (.TableT addr lim rt) n n1).2
            ⟨by rw [tabletype_replace];exact ht.1,ht.2⟩
          apply Eval.call
          change Eval Body (tryClauses (SpecTec.Table_ok_clauses (replace refs c) _)) n _ finish
          apply tryClauses_cons_success
          unfold SpecTec.«Table_ok:clause:0»
          apply Eval.bind_success ht'
          apply Eval.bind_success (ConstructiveRefs.const_ok_replace_refs c refs (.RefT rt) code n1 finish ha hc)
          exact Eval.pure _
    | orElse_unmatch hfailedSupply h => restore_supply hfailedSupply at h; cases h

theorem tables_replace (refs : SpecTec.free) (c out : context) (xs : List SpecTec.table) (n finish : Nat)
    (ha : ∀item∈xs,Available refs item.TINIT)
    (h : Eval Body (.call ⟨context,Call.Tables_ok c xs⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Tables_ok (replace refs c) xs⟩)
      n (.success (.of (replace refs out))) finish := by
  induction xs generalizing c n with
  | nil =>
    obtain ⟨he,hn⟩ := (TablesDecision.tables_nil_success_iff c out n finish).1 h
    exact (TablesDecision.tables_nil_success_iff _ _ n finish).2 ⟨congrArg (replace refs) he,hn⟩
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := (TablesDecision.tables_cons_success_iff c out item xs n finish).1 h
    exact (TablesDecision.tables_cons_success_iff _ _ item xs n finish).2
      ⟨replace refs next,middle,table_replace refs c next item n middle (ha item (by simp)) hh,
        ih next middle (fun item hm => ha item (by simp [hm])) ht⟩

theorem tables_bounded (c out : context) (xs : List SpecTec.table) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Tables_ok c xs⟩) n (.success (.of out)) finish) :
    ∀item∈xs,∀x,instr.«REF.FUNC» x∈item.TINIT → x<c.FUNCS.length := by
  induction xs generalizing c n with
  | nil => simp
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := (TablesDecision.tables_cons_success_iff c out item xs n finish).1 h
    intro entry hm x hx
    rcases List.mem_cons.mp hm with he|hm
    · subst entry
      obtain ⟨t,a,b,hc⟩ := DeclarationConstValidation.table_ok_initializer_const c next item n middle hh
      exact ConstructiveModuleRefsBounds.constant_bound c t item.TINIT a b hc x hx
    · have hb := ih next middle ht entry hm x hx
      simpa [CandidateProvenancePreGlobals.table_ok_funcs c next item n middle hh] using hb

theorem global_replace (refs : SpecTec.free) (c out : context) (item : SpecTec.global) (n finish : Nat)
    (ha : Available refs item.GINIT)
    (h : Eval Body (.call ⟨context,Call.Global_ok c item⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Global_ok (replace refs c) item⟩)
      n (.success (.of (replace refs out))) finish := by
  rcases item with ⟨⟨mu,t⟩,code⟩
  cases h with | call h =>
    change Eval Body (.orElse (SpecTec.«Global_ok:clause:0» c _) (fun _ => .unmatch)) n _ finish at h
    cases h with
    | orElse_success h =>
      unfold SpecTec.«Global_ok:clause:0» at h
      cases h with | bind_success htype h =>
        rename_i n1 unit
        cases unit
        cases h with | bind_success hc hp =>
          cases hp
          have ht := (GlobaltypeValidation.globaltype_success_iff_valid c (.GlobalT mu t) n n1).1 htype
          have ht' := (GlobaltypeValidation.globaltype_success_iff_valid (replace refs c) (.GlobalT mu t) n n1).2
            ⟨by rw [globaltype_replace];exact ht.1,ht.2⟩
          apply Eval.call
          change Eval Body (tryClauses (SpecTec.Global_ok_clauses (replace refs c) _)) n _ finish
          apply tryClauses_cons_success
          unfold SpecTec.«Global_ok:clause:0»
          apply Eval.bind_success ht'
          apply Eval.bind_success (ConstructiveRefs.const_ok_replace_refs c refs (t) code n1 finish ha hc)
          exact Eval.pure _
    | orElse_unmatch hfailedSupply h => restore_supply hfailedSupply at h; cases h

theorem globals_replace (refs : SpecTec.free) (c out : context) (xs : List SpecTec.global) (n finish : Nat)
    (ha : ∀item∈xs,Available refs item.GINIT)
    (h : Eval Body (.call ⟨context,Call.Globals_ok c xs⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Globals_ok (replace refs c) xs⟩)
      n (.success (.of (replace refs out))) finish := by
  induction xs generalizing c n with
  | nil =>
    obtain ⟨he,hn⟩ := (GlobalsDecision.globals_nil_success_iff c out n finish).1 h
    exact (GlobalsDecision.globals_nil_success_iff _ _ n finish).2 ⟨congrArg (replace refs) he,hn⟩
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := (GlobalsDecision.globals_cons_success_iff c out item xs n finish).1 h
    exact (GlobalsDecision.globals_cons_success_iff _ _ item xs n finish).2
      ⟨replace refs next,middle,global_replace refs c next item n middle (ha item (by simp)) hh,
        ih next middle (fun item hm => ha item (by simp [hm])) ht⟩

theorem global_ok_funcs
    (c out : SpecTec.context) (t : SpecTec.global)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Global_ok c t⟩)
      start (.success (.of out)) finish) :
    out.FUNCS = c.FUNCS := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Global_ok_clauses c t))
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hclause =>
          unfold SpecTec.«Global_ok:clause:0» at hclause
          cases hclause with
          | bind_success _ htail =>
              cases htail with
              | bind_success _ hpure =>
                  cases hpure with
                  | pure => rfl
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone


theorem globals_bounded (c out : context) (xs : List SpecTec.global) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Globals_ok c xs⟩) n (.success (.of out)) finish) :
    ∀item∈xs,∀x,instr.«REF.FUNC» x∈item.GINIT → x<c.FUNCS.length := by
  induction xs generalizing c n with
  | nil => simp
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := (GlobalsDecision.globals_cons_success_iff c out item xs n finish).1 h
    intro entry hm x hx
    rcases List.mem_cons.mp hm with he|hm
    · subst entry
      obtain ⟨t,a,b,hc⟩ := DeclarationConstValidation.global_ok_initializer_const c next item n middle hh
      exact ConstructiveModuleRefsBounds.constant_bound c t item.GINIT a b hc x hx
    · have hb := ih next middle ht entry hm x hx
      simpa [global_ok_funcs c next item n middle hh] using hb

#print axioms tables_replace
#print axioms globals_replace
#print axioms tables_bounded
#print axioms globals_bounded
end properties.wasm_module_ok.ConstructiveModuleInitializerRefs
