import properties.wasm_module_ok.ConstructiveBodyBranchTable
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
import properties.wasm_module_ok.ConstructiveBodyOperatorCalls
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBranchTableCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyLookup ConstructiveBodyBranchTable ConstructiveBodyProductionCoverage


theorem iter_complete (c : context) (env : Env c) (actual : List valtype)
    (ha : ∀t∈actual,CandidateValMatch.InTableVal c t) (xs : List Nat) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.«Instr_ok:br_table:iter:4» c actual xs⟩) start (.success (.of ())) finish) :
    ∃ys : List (Target c actual),indices ys=xs ∧ finish=start := by
  induction xs generalizing start finish with
  | nil =>
    exact ⟨[],rfl,(properties.wasm_module_ok.Execution.eval_deterministic h (targets_call c actual [] env ha start)).2⟩
  | cons x xs ih =>
    cases h with | call h =>
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«Instr_ok:br_table:iter:4_clauses» c actual (x::xs)))
       start (.success (.of ())) finish at h
     cases h with
     | orElse_success h => cases h
     | orElse_unmatch hfailedSupply h =>
       restore_supply hfailedSupply at h
       cases h with
       | orElse_unmatch hfailedSupply h => restore_supply hfailedSupply at h; cases h
       | orElse_success h =>
         unfold SpecTec.«Instr_ok:br_table:iter:4:clause:1» at h
         cases hx : c.LABELS[x]? with
         | none => simp only [hx] at h; cases h
         | some ts =>
           simp only [hx] at h
           cases h with | bind_success hm h =>
            cases h with | bind_success ht hp =>
             cases hp
             have hb := env.labels ts (List.mem_iff_getElem?.mpr ⟨x,hx⟩)
             have matched := MatchResulttypeDecision.match_pairs_of_resulttype_success c actual ts _ _ env.ready ha hb hm
             have counter := MatchResulttypeDecision.match_resulttype_success_counter c actual ts _ _ env.ready ha hb hm
             obtain ⟨ys,he,hcounter⟩ := ih _ _ ht
             exact ⟨⟨⟨x,ts,hx⟩,matched⟩::ys,by simpa only [indices,List.map_cons] using congrArg (x::·) he,hcounter.trans counter⟩

theorem production_member (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (base : Entry c.LABELS)
    (hm : MatchResulttypeDecision.matchPairs c (ConstructiveBodyInitTypes.operandTypes stack base.value.length) base.value=true) :
    production c stack env hs base hm∈productions c stack env hs := by
  apply List.mem_flatMap.mpr
  refine ⟨base,ConstructiveBodyLookup.complete _ base,?_⟩
  simp only [hm,dif_pos]
  exact List.mem_singleton_self _

theorem production_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (base : Entry c.LABELS)
    (hm : MatchResulttypeDecision.matchPairs c (ConstructiveBodyInitTypes.operandTypes stack base.value.length) base.value=true)
    (xs : List (Target c (ConstructiveBodyInitTypes.operandTypes stack base.value.length))) :
    Produces (production c stack env hs base hm) (.BR_TABLE (indices xs) base.index) := by
  refine ⟨⟨.BR_TABLE (indices xs) base.index,fun n => branchTable c stack env hs base hm xs n⟩,?_,rfl⟩
  exact ⟨xs,lists_complete c _ ⟨base,hm⟩ xs,rfl⟩

theorem original (c : context) (stack : inferresulttype) (env : Env c) (hstack : StackBacked c stack)
    (xs : List Nat) (y : Nat) (result : inferinstrtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_TABLE xs y)⟩)
      start (.success (.of result)) finish) :
    Covers (productions c stack env hstack) (.BR_TABLE xs y) result ∧ finish=start := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_TABLE xs y) 10 (by decide) rfl (by decide) result start finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:10» c stack (.BR_TABLE xs y)) start _ finish at hs
  unfold SpecTec.«Instr_ok:clause:10» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hy : c.LABELS[y]? with
    | none => simp only [hy] at tail; cases tail
    | some ts =>
      simp only [hy] at tail
      cases tail with | bind_success hi tail =>
       obtain ⟨he,_⟩ := (ConstructiveBodyInitTypes.zero_exact stack ts.length _ _ _).1 hi
       cases he
       cases tail with | bind_success hm tail =>
        cases tail with | bind_success _ tail =>
         cases tail with | bind_success ht hp =>
          cases hp
          let base : Entry c.LABELS := ⟨y,ts,hy⟩
          have ha := ConstructiveBodyInitTypes.prefix_backed c stack hstack ts.length
          have hmatch := MatchResulttypeDecision.match_pairs_of_resulttype_success c _ ts _ _ env.ready ha
            (env.labels ts (List.mem_iff_getElem?.mpr ⟨y,hy⟩)) hm
          obtain ⟨ys,he,_⟩ := iter_complete c env _ ha xs _ _ ht
          have total := branchTable c stack env hstack base hmatch ys start
          simp only [he] at total
          obtain ⟨hr,hcounter⟩ := ConstructiveBodyOperatorCalls.effect_unique c stack (.BR_TABLE xs y) _ _ start _ total h
          refine ⟨⟨production c stack env hstack base hmatch,production_member c stack env hstack base hmatch,hr.symm,?_⟩,hcounter⟩
          simpa only [he] using production_produces c stack env hstack base hmatch ys

#print axioms original
end properties.wasm_module_ok.ConstructiveBodyBranchTableCoverage
