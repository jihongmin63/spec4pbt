import properties.wasm_module_ok.ConstructiveConstTreeCoverage
import properties.wasm_module_ok.ConstFinalPopMatch
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTreeTarget
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveConstTree properties.wasm_module_ok.ConstructiveConstTreeCoverage

theorem output_in_table (c : context) (hp : CandidateUniverseReady.Provenance c)
    (tree : Tree) (h : Good c tree) : CandidateValMatch.InTableVal c tree.output := by
  cases h with
  | node i u children need hs hi hm hk =>
    have ht := ConstCandidateTableMembership.constant_instruction_outputs_in_table c
      (.NoEllipses,[]++outputs children) i (effect need u) 0 0 hs (hi [] 0) hp
    exact ht u (by simp [effect])

/-- The typed tree keeps the original target coercion as well as the code. -/
theorem const_tree_target (c : context)
    (hr : CandidateTypeReady.Ready c) (hp : CandidateUniverseReady.Provenance c)
    (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Const_ok c target xs⟩)
      start (.success (.of ())) finish) :
    ∃ tree,Good c tree ∧ tree.code=xs ∧ ∀ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,Call.Match_resulttype c [tree.output] [target]⟩)
        n (.success (.of ())) n := by
  obtain ⟨tree,hgood,hcode⟩ := const_tree c hr hp hn target xs start finish h
  refine ⟨tree,hgood,hcode,?_⟩
  obtain ⟨hs,irt,indices,ell,middle,hxs,hpop⟩ :=
    (ConstDecisionTrace.const_ok_decision_trace_iff c target xs start finish).1 h
  have hknown := ConstConstructiveTrace.trace_to_instrs (tree_trace c tree hgood [] start)
  have hknown' : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferresulttype × List idx,Call.Instrs_ok c (.NoEllipses,[]) xs⟩)
      start (.success (.of (((.NoEllipses,[tree.output]),[]) : inferresulttype × List idx))) start := by
    simpa only [List.nil_append,hcode] using hknown
  obtain ⟨he,hsupply⟩ := properties.wasm_module_ok.Execution.eval_deterministic hxs hknown'
  cases he
  obtain ⟨a,b,hm⟩ := ConstFinalPopMatch.final_const_pop_matches c target tree.output ell middle finish hpop
  have hactual : ∀ t∈[tree.output],CandidateValMatch.InTableVal c t := by
    intro t ht
    have he : t=tree.output := by simpa using ht
    subst t
    exact output_in_table c hp tree hgood
  have hrequired : ∀ t∈[target],CandidateValMatch.InTableVal c t := by simpa using ht
  have hpairs := MatchResulttypeDecision.match_pairs_of_resulttype_success c _ _ a b hr hactual hrequired hm
  intro n
  exact (MatchResulttypeDecision.match_pairs_iff_resulttype c _ _ n hr hactual hrequired).1 hpairs

#print axioms const_tree_target
end properties.wasm_module_ok.ConstructiveConstTreeTarget
