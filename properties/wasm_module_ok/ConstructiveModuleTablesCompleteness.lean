import properties.wasm_module_ok.ConstructiveModuleTables
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleTables
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans

theorem step_complete (c out : context) (env : Env c) (item : SpecTec.table)
    (h : TableDecision.tableResult c item=some out) :
    ∃round,∃g∈constructors c env round,∃head : Step c,
      Gen.support g.generator head ∧ head.item=item ∧ head.after=out := by
  rcases item with ⟨⟨addr,lim,rt⟩,init⟩
  obtain ⟨hv,ho⟩ := (TableDecision.table_result_iff_valid c out _).1 h
  have parts : TabletypeValidation.tabletypeValid c (.TableT addr lim rt)=true ∧
      ConstExpressionDecision.constantExpressionResult c (.RefT rt) init=true := by
    simpa [TableDecision.tableValid] using hv
  have tv : ReftypeTotal.reftypeValid c rt=true ∧ LimitsValidation.limitsValid (bound addr) lim=true := by
    cases addr <;> simpa [TabletypeValidation.tabletypeValid,bound] using parts.1
  have ht : ValtypeValidation.valtypeValid c (.RefT rt)=true := by
    cases rt; exact tv.1
  have hl := tv.2
  let target : Source c := ⟨.RefT rt,ht⟩
  let code : Constant c (.RefT rt) := ⟨init,fun n =>
    (ConstExpressionDecision.constant_expression_result_iff_const_ok c (.RefT rt) init n
      env.ready env.provenance env.nested (backed c target)).1 parts.2⟩
  obtain ⟨round,⟨source,plan⟩,hp,he⟩ := plans_complete c env target init 0 0 (code.property 0)
  change source=target at he
  subst source
  let p : Productive c env := ⟨target,plan⟩
  let ext : Extent addr := ⟨lim,hl⟩
  refine ⟨round,branch c env p rt rfl addr,?_,step c env p rt rfl addr ext code,?_,rfl,ho.symm⟩
  · apply List.mem_flatMap.mpr
    refine ⟨p,hp,?_⟩
    cases addr <;> simp [p,target]
  · refine ⟨ext,?_,code,expressions_complete c env p code,rfl⟩
    rw [extents,ConstructiveAttach.refine_support,ConstructiveLimits.limits_support]
    exact hl

theorem sized_cons (depth round : Nat) (c : context) (env : Env c)
    (g : Audited (Step c)) (hg : g∈constructors c env round) (head : Step c)
    (hh : Gen.support g.generator head) (tail : Result head.after)
    (ht : Gen.support (sized depth head.after head.env).generator tail) :
    Gen.support (sized (depth+1) c env).generator (cons c head tail) := by
  refine ⟨round,by simp,?_⟩
  apply (merge_support _ _ _).2
  refine ⟨g.bind (fun s => (sized depth s.after s.env).map (cons c s)),?_,?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g,hg,rfl⟩)
  · exact ⟨head,hh,tail,ht,rfl⟩

theorem sized_complete (c result : context) (env : Env c) (xs : List SpecTec.table)
    (h : TablesDecision.tablesResult c xs=some result) :
    ∃out : Result c, Gen.support (sized xs.length c env).generator out ∧ out.items=xs ∧ out.after=result := by
  induction xs generalizing c with
  | nil =>
    have he : c=result := Option.some.inj h
    exact ⟨done c env,rfl,rfl,he⟩
  | cons x xs ih =>
    cases hh : TableDecision.tableResult c x with
    | none => simp [TablesDecision.tablesResult,hh] at h
    | some next =>
      have ht : TablesDecision.tablesResult next xs=some result := by
        simpa only [TablesDecision.tablesResult,hh,Option.bind_some] using h
      obtain ⟨round,g,hg,head,hhead,he,ho⟩ := step_complete c next env x hh
      rw [←ho] at ht
      obtain ⟨tail,hg',hxs,hout⟩ := ih head.after head.env ht
      exact ⟨cons c head tail,sized_cons xs.length round c env g hg head hhead tail hg',by simp [cons,he,hxs],hout⟩

theorem generate_complete (c result : context) (env : Env c) (xs : List SpecTec.table)
    (start finish : Nat) (h : SpecTecExecution.Eval Body
      (.call ⟨context,Call.Tables_ok c xs⟩) start (.success (.of result)) finish) :
    ∃out : Result c, Gen.support (generate c env) out ∧ out.items=xs ∧ out.after=result := by
  have hr := (TablesDecision.tables_result_iff_call c result xs start finish
    env.ready env.provenance env.nested).2 h |>.1
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result env xs hr
  exact ⟨out,⟨xs.length,by simp,hg⟩,hs,ho⟩

#print axioms generate_complete
end properties.wasm_module_ok.ConstructiveModuleTables
