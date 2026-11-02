import properties.wasm_module_ok.ConstructiveModuleGlobals
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleGlobals
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans

theorem step_complete (c out : context) (env : Env c) (item : SpecTec.global)
    (h : GlobalDecision.globalResult c item=some out) :
    ∃round,∃g∈constructors c env round,∃head : Step c,
      Gen.support g.generator head ∧ head.item=item ∧ head.after=out := by
  rcases item with ⟨⟨mu,t⟩,init⟩
  obtain ⟨hv,ho⟩ := (GlobalDecision.global_result_iff_valid c out _).1 h
  have parts : ValtypeValidation.valtypeValid c t=true ∧
      ConstExpressionDecision.constantExpressionResult c t init=true := by
    simpa [GlobalDecision.globalValid,GlobaltypeValidation.globaltypeValid] using hv
  let target : Source c := ⟨t,parts.1⟩
  let code : Constant c t := ⟨init,fun n =>
    (ConstExpressionDecision.constant_expression_result_iff_const_ok c t init n
      env.ready env.provenance env.nested (backed c target)).1 parts.2⟩
  obtain ⟨round,⟨source,plan⟩,hp,he⟩ := plans_complete c env target init 0 0 (code.property 0)
  change source=target at he
  subst source
  let p : Productive c env := ⟨target,plan⟩
  refine ⟨round,(expressions c env p).map (step c env p mu),?_,step c env p mu code,?_,rfl,ho.symm⟩
  · exact List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨mu,by cases mu <;> simp,rfl⟩⟩
  · exact ⟨code,expressions_complete c env p code,rfl⟩

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

theorem sized_complete (c result : context) (env : Env c) (xs : List SpecTec.global)
    (h : GlobalsDecision.globalsResult c xs=some result) :
    ∃out : Result c, Gen.support (sized xs.length c env).generator out ∧ out.items=xs ∧ out.after=result := by
  induction xs generalizing c with
  | nil =>
    have he : c=result := Option.some.inj h
    exact ⟨done c env,rfl,rfl,he⟩
  | cons x xs ih =>
    cases hh : GlobalDecision.globalResult c x with
    | none => simp [GlobalsDecision.globalsResult,hh] at h
    | some next =>
      have ht : GlobalsDecision.globalsResult next xs=some result := by
        simpa only [GlobalsDecision.globalsResult,hh,Option.bind_some] using h
      obtain ⟨round,g,hg,head,hhead,he,ho⟩ := step_complete c next env x hh
      rw [←ho] at ht
      obtain ⟨tail,hg',hxs,hout⟩ := ih head.after head.env ht
      exact ⟨cons c head tail,sized_cons xs.length round c env g hg head hhead tail hg',by simp [cons,he,hxs],hout⟩

theorem generate_complete (c result : context) (env : Env c) (xs : List SpecTec.global)
    (start finish : Nat) (h : SpecTecExecution.Eval Body
      (.call ⟨context,Call.Globals_ok c xs⟩) start (.success (.of result)) finish) :
    ∃out : Result c, Gen.support (generate c env) out ∧ out.items=xs ∧ out.after=result := by
  have hr := (GlobalsDecision.globals_result_iff_call c result xs start finish
    env.ready env.provenance env.nested).2 h |>.1
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result env xs hr
  exact ⟨out,⟨xs.length,by simp,hg⟩,hs,ho⟩

#print axioms generate_complete
end properties.wasm_module_ok.ConstructiveModuleGlobals
