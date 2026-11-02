import properties.wasm_module_ok.ConstructiveConstTreeStep
import properties.wasm_module_ok.ConstTraceNestedReady
import properties.wasm_module_ok.ConstFinalPopShape
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTreeCoverage
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveConstTree properties.wasm_module_ok.ConstructiveConstTreeStep

/-- Parse an original successful sequence, retaining its exact postfix order. -/
theorem instrs_forest (c : context)
    (hr : CandidateTypeReady.Ready c) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (xs : List instr)
    (hs : ∀ i∈xs,ConstAdditionalSyntaxValidation.Syntax c i)
    (forest : List Tree) (hf : ∀ t∈forest,Good c t)
    (ha : ∀ t∈outputs forest,CandidateValMatch.InTableVal c t)
    (result : inferresulttype × List idx) (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype × List idx,SpecTecCall.Instrs_ok c (.NoEllipses,outputs forest) xs⟩)
      start (.success (.of result)) finish) :
    ∃ trees, (∀ t∈trees,Good c t) ∧ result.1=(.NoEllipses,outputs trees) ∧
      trees.flatMap Tree.code=forest.flatMap Tree.code++xs := by
  induction xs generalizing forest start with
  | nil =>
    have he := ((InstrsValidation.instrs_nil_success_iff c _ result start finish).1 hcall).1
    refine ⟨forest,hf,?_,by simp⟩
    exact congrArg Prod.fst he
  | cons i xs ih =>
    obtain ⟨iit,next,popped,pushed,m1,m2,m3,m4,hi,hin,hpop,hpush,htail⟩ :=
      (InstrsValidation.instrs_cons_success_iff c _ i xs result start finish).1 hcall
    have hsi := hs i (by simp)
    have hconst := ConstAdditionalSyntaxValidation.syntax_is_const c i start hsi
    obtain ⟨need,hins,hlocals⟩ := ConstInstrDecision.syntax_instruction_input_shape c _ i iit start m1 hsi hi
    obtain ⟨u,houts⟩ := ConstSyntaxSingleton.syntax_instruction_singleton_outputs c _ i iit start m1 hsi hi
    have heffect : iit=effect need u := by
      rcases iit with ⟨it,locals⟩
      cases it
      simp only at hins houts hlocals
      subst locals
      cases hins
      cases houts
      rfl
    have heNext : next=c := by
      have he := ((LocalInitValidation.init_locals_success_iff_result c iit.2 next m1 m2).1 hin).1
      simpa [hlocals,LocalInitValidation.initLocalsResult] using he.symm
    subst next
    have hrequired := ConstExtendedCandidateReady.is_const_instruction_inputs_in_table
      c (.NoEllipses,outputs forest) i iit start start m1 hconst hi hp hn
    have houtTable := ConstCandidateTableMembership.is_const_instruction_outputs_in_table
      c (.NoEllipses,outputs forest) i iit start start m1 hconst hi hp
    have hi' : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs forest) i⟩)
        start (.success (.of (effect need u))) m1 := by simpa only [heffect] using hi
    have hpop' : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨inferresulttype,SpecTecCall.«$pop» c (.NoEllipses,need) (.NoEllipses,outputs forest)⟩)
        m2 (.success (.of popped)) m3 := by simpa only [hins] using hpop
    have hn' : ∀ t∈need,CandidateValMatch.InTableVal c t := by simpa only [hins] using hrequired
    have hu : CandidateValMatch.InTableVal c u := houtTable u (by simp [houts])
    have hgood := attach_good c forest i u need popped start m1 m2 m3 hr hsi hf ha hn' hi' hpop'
    have hpopResult := PopResult.pop_noellipses_success_result c need (outputs forest) popped m2 m3 hpop'
    have hpushResult := ((PushValidation.push_success_iff_result c iit.1.OUTS popped pushed m3 m4).1 hpush).1
    have hpushed : pushed=(.NoEllipses,outputs (attach forest need.length i u)) := by
      rw [attach_outputs]
      simpa only [houts,hpopResult,PushValidation.pushResult,Option.some.injEq] using hpushResult.symm
    have haNew : ∀ t∈outputs (attach forest need.length i u),CandidateValMatch.InTableVal c t := by
      intro t ht
      rw [attach_outputs] at ht
      rcases List.mem_append.1 ht with ht | ht
      · exact ha t (List.mem_of_mem_take ht)
      · have he : t=u := by simpa using ht
        simpa only [he] using hu
    obtain ⟨trees,hg,he,hcode⟩ := ih (fun j hj => hs j (by simp [hj]))
      (attach forest need.length i u) hgood haNew m4 (by simpa only [hpushed] using htail)
    refine ⟨trees,hg,he,?_⟩
    rw [hcode,attach_code,List.append_assoc]
    rfl

/-- Every original constant expression in a ready/provenance-established
prefix is represented by one typed tree with exactly the original code. -/
theorem const_tree (c : context)
    (hr : CandidateTypeReady.Ready c) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩)
      start (.success (.of ())) finish) :
    ∃ tree,Good c tree ∧ tree.code=xs := by
  obtain ⟨hs,irt,indices,ell,middle,hxs,hpop⟩ :=
    (ConstDecisionTrace.const_ok_decision_trace_iff c target xs start finish).1 h
  obtain ⟨trees,hg,he,hcode⟩ := instrs_forest c hr hp hn xs
    (fun i hi => (ConstSyntaxDecision.syntaxAllowed_iff c i).1 (hs i hi))
    [] (by simp) (by simp [outputs]) (irt,indices) start middle hxs
  have he' : irt=(.NoEllipses,outputs trees) := he
  rw [he'] at hpop
  obtain ⟨u,hu,_⟩ := ConstFinalPopShape.final_const_pop_singleton c target (outputs trees) ell middle finish hpop
  have hlen : trees.length=1 := by
    have hh := congrArg List.length hu
    simpa [outputs] using hh
  obtain ⟨tree,rfl⟩ := List.length_eq_one_iff.1 hlen
  refine ⟨tree,hg tree (by simp),?_⟩
  simpa using hcode

/-- No readiness or provenance side condition is missing for backward module
coverage: the original successful trace supplies it at every constant stage. -/
theorem module_const_tree (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) (c : context)
    (hc : c∈[tr.c0,tr.c1,tr.c2,tr.c3,tr.c4,tr.c5,tr.c6,tr.c7,tr.c8])
    (target : valtype) (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩)
      start (.success (.of ())) finish) :
    ∃ tree,Good c tree ∧ tree.code=xs :=
  const_tree c (CandidateTraceReady.trace_ready_at m tr c hc)
    (CandidateTraceReady.trace_provenance_at m tr c hc)
    (ConstTraceNestedReady.trace_nested_ready_at m tr c hc) target xs start finish h

#print axioms module_const_tree
end properties.wasm_module_ok.ConstructiveConstTreeCoverage
