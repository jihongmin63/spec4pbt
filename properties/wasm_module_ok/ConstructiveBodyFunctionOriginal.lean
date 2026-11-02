import properties.wasm_module_ok.ConstructiveBodyFunctionProductions
import properties.wasm_module_ok.ConstructiveBodyOperatorCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyFunctionMetadata ConstructiveBodyEnvironment ConstructiveBodyFunctionProductions

theorem signature_of_type (c : context) (x : Nat) (ft : functype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨functype,SpecTecCall.«$func_type» c x⟩) n (.success (.of ft)) finish) :
    ∃sig : Signature c.TYPES,sig.entry.index=x ∧ ft=.FuncT sig.inputs sig.outputs ∧ finish=n := by
  obtain ⟨dt,hx,hex⟩ := (FunctionTypeValidation.func_type_success_iff c x ft n finish).1 h
  obtain ⟨he,hn⟩ := (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT ft) n finish).1 hex
  cases ft with | FuncT ins outs =>
   exact ⟨⟨⟨x,dt,hx⟩,ins,outs,he⟩,rfl,rfl,hn⟩

theorem direct (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL x)⟩) n (.success (.of effect)) finish) :
    ∃sig : Signature c.FUNCS,sig.entry.index=x := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.CALL x) 15 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:15» c stack (.CALL x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:15» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.FUNCS[x]? with
    | none => rw [hx] at tail; cases tail
    | some dt =>
      rw [hx] at tail
      cases tail with | bind_success hex tail =>
       rename_i middle st
       cases tail with | bind_success hft tail =>
        rename_i middle2 ft
        obtain ⟨heq,_⟩ := (StartValidation.functype_of_strtype_success_iff st ft middle middle2).1 hft
        subst st
        obtain ⟨he,_⟩ := (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT ft) n middle).1 hex
        cases ft with | FuncT ins outs => exact ⟨⟨⟨x,dt,hx⟩,ins,outs,he⟩,rfl⟩

theorem reference (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL_REF x)⟩) n (.success (.of effect)) finish) :
    ∃sig : Signature c.TYPES,sig.entry.index=x := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.CALL_REF x) 16 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:16» c stack (.CALL_REF x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:16» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hft _ =>
    obtain ⟨sig,hi,_,_⟩ := signature_of_type c x _ _ _ hft
    exact ⟨sig,hi⟩

theorem returnDirect (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL x)⟩) n (.success (.of effect)) finish) :
    ∃sig : Signature c.FUNCS,sig.entry.index=x ∧ MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL x) 19 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:19» c stack (.RETURN_CALL x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:19» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.FUNCS[x]? with
    | none => rw [hx] at tail; cases tail
    | some dt =>
      rw [hx] at tail
      cases tail with | bind_success hex tail =>
       rename_i middle st
       cases tail with | bind_success hft tail =>
        rename_i middle2 ft
        obtain ⟨heq,_⟩ := (StartValidation.functype_of_strtype_success_iff st ft middle middle2).1 hft
        subst st
        obtain ⟨he,_⟩ := (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT ft) n middle).1 hex
        cases ft with | FuncT ins outs =>
         let sig : Signature c.FUNCS := ⟨⟨x,dt,hx⟩,ins,outs,he⟩
         cases tail with | bind_success hmatch tail =>
          cases tail with | bind_success hguard _ =>
           cases hguard with | guard_true htrue =>
            have hm := (ConstructiveBodyMatchers.result_exact c sig.outputs c.RESULTS _ _ _ env.ready
              (fun t ht => sig.backed env env.provenance.funcs t (List.mem_append_right _ ht)) env.results).1 hmatch
            exact ⟨sig,rfl,hm.1.symm.trans htrue⟩

theorem returnReference (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL_REF x)⟩) n (.success (.of effect)) finish) :
    ∃sig : Signature c.TYPES,sig.entry.index=x ∧ MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL_REF x) 20 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:20» c stack (.RETURN_CALL_REF x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:20» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hft tail =>
    obtain ⟨sig,hi,hftEq,_⟩ := signature_of_type c x _ _ _ hft
    rw [hftEq] at tail
    cases tail with | bind_success hmatch tail =>
     cases tail with | bind_success hguard _ =>
      cases hguard with | guard_true htrue =>
       have hm := (ConstructiveBodyMatchers.result_exact c sig.outputs c.RESULTS _ _ _ env.ready
         (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht)) env.results).1 hmatch
       exact ⟨sig,hi,hm.1.symm.trans htrue⟩

theorem indirect (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL_INDIRECT x y)⟩) n (.success (.of effect)) finish) :
    ∃(tab : FunctionTable c) (sig : Signature c.TYPES),tab.index=x ∧ sig.entry.index=y := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.CALL_INDIRECT x y) 17 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:17» c stack (.CALL_INDIRECT x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:17» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.TABLES[x]? with
    | none => rw [hx] at tail; cases tail
    | some tab =>
      rw [hx] at tail
      cases tab with | TableT addr lim rt =>
       cases tail with | bind_success hft tail =>
        obtain ⟨sig,hi,hftEq,_⟩ := signature_of_type c y _ _ _ hft
        rw [hftEq] at tail
        cases tail with | bind_success hmatch tail =>
         cases tail with | bind_success hguard tail =>
          cases hguard with | guard_true htrue =>
           have hm := (ConstructiveBodyReferenceMatcher.exact_call c rt (.«% %» .Null .FuncHT) _ _ _ env.ready
             (env.tables addr lim rt (List.mem_iff_getElem?.mpr ⟨x,hx⟩))
             (ConstructiveBodyReferenceMatcher.base_backed c .Null .FuncHT (by simp [HeaptypeValidation.baseHeaptypes]))).1 hmatch
           let table : FunctionTable c := ⟨x,addr,lim,rt,hx,hm.1.symm.trans htrue⟩
           exact ⟨table,sig,rfl,hi⟩

theorem returnIndirect (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL_INDIRECT x y)⟩) n (.success (.of effect)) finish) :
    ∃(tab : FunctionTable c) (sig : Signature c.TYPES),tab.index=x ∧ sig.entry.index=y ∧ MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.RETURN_CALL_INDIRECT x y) 21 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:21» c stack (.RETURN_CALL_INDIRECT x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:21» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.TABLES[x]? with
    | none => rw [hx] at tail; cases tail
    | some tab =>
      rw [hx] at tail
      cases tab with | TableT addr lim rt =>
       cases tail with | bind_success hft tail =>
        obtain ⟨sig,hi,hftEq,_⟩ := signature_of_type c y _ _ _ hft
        rw [hftEq] at tail
        cases tail with | bind_success hmatch tail =>
         cases tail with | bind_success hguard tail =>
          cases hguard with | guard_true htrue =>
           have hm := (ConstructiveBodyReferenceMatcher.exact_call c rt (.«% %» .Null .FuncHT) _ _ _ env.ready
             (env.tables addr lim rt (List.mem_iff_getElem?.mpr ⟨x,hx⟩))
             (ConstructiveBodyReferenceMatcher.base_backed c .Null .FuncHT (by simp [HeaptypeValidation.baseHeaptypes]))).1 hmatch
           let table : FunctionTable c := ⟨x,addr,lim,rt,hx,hm.1.symm.trans htrue⟩
           cases tail with | bind_success hresult tail =>
            cases tail with | bind_success hguard _ =>
             cases hguard with | guard_true htrue =>
              have hr := (ConstructiveBodyMatchers.result_exact c sig.outputs c.RESULTS _ _ _ env.ready
                (fun t ht => sig.backed env (fun _ h => h) t (List.mem_append_right _ ht)) env.results).1 hresult
              exact ⟨table,sig,rfl,hi,hr.1.symm.trans htrue⟩

theorem throwTag (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.THROW x)⟩) n (.success (.of effect)) finish) :
    ∃tag : ConstructiveBodyTagMetadata.Tag c,tag.index=x := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.THROW x) 22 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:22» c stack (.THROW x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:22» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.TAGS[x]? with
    | none => rw [hx] at tail; cases tail
    | some tag =>
      rw [hx] at tail
      cases tag with | TagT dt =>
       cases tail with | bind_success hex tail =>
        rename_i middle st
        cases tail with | bind_success hft tail =>
         rename_i middle2 ft
         obtain ⟨heq,_⟩ := (StartValidation.functype_of_strtype_success_iff st ft middle middle2).1 hft
         subst st
         obtain ⟨he,_⟩ := (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT ft) n middle).1 hex
         cases ft with | FuncT ins outs => exact ⟨⟨x,dt,ins,outs,hx,he⟩,rfl⟩

#print axioms returnIndirect
#print axioms throwTag
end properties.wasm_module_ok.ConstructiveBodyFunctionOriginal
