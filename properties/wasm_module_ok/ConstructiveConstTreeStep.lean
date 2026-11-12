import properties.wasm_module_ok.ConstructiveConstTree
import properties.wasm_module_ok.ConstructiveConstFrame
import properties.wasm_module_ok.MatchResulttypeDecision
import properties.wasm_module_ok.PopMatchExtraction
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTreeStep
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveConstTree properties.wasm_module_ok.ConstructiveConstFrame

/-- Turn one original successful stack action into a typed postfix node.
No AST is tested; this is backward decomposition of the supplied derivation. -/
theorem attach_good (c : context) (forest : List Tree) (i : instr) (u : valtype)
    (need : List valtype) (popped : inferresulttype) (start finish ps pf : Nat)
    (hr : CandidateTypeReady.Ready c)
    (hs : ConstAdditionalSyntaxValidation.Syntax c i)
    (hf : ∀ t∈forest,Good c t)
    (ha : ∀ t∈outputs forest,CandidateValMatch.InTableVal c t)
    (hn : ∀ t∈need,CandidateValMatch.InTableVal c t)
    (hi : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c (.NoEllipses,outputs forest) i⟩)
      start (.success (.of (effect need u))) finish)
    (hp : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferresulttype,Call.«$pop» c (.NoEllipses,need) (.NoEllipses,outputs forest)⟩)
      ps (.success (.of popped)) pf) :
    ∀ t∈attach forest need.length i u,Good c t := by
  obtain ⟨hlen,ms,hm⟩ := PopMatchExtraction.pop_noellipses_success_has_match c need
    (outputs forest) popped ps pf hp
  have hlenf : need.length≤forest.length := by simpa [outputs] using hlen
  let k := forest.length-need.length
  have houtputs : outputs (forest.drop k)=(outputs forest).drop k := by simp [outputs]
  have hcut : (outputs forest).length-need.length=k := by simp [outputs,k]
  have hmatch : ∀ n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Match_resulttype c (outputs (forest.drop k)) need⟩)
      n (.success (.of ())) n := by
    intro n
    have htable : ∀ t∈(outputs forest).drop k,CandidateValMatch.InTableVal c t :=
      fun t ht => ha t (List.mem_of_mem_drop ht)
    have hm' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,Call.Match_resulttype c ((outputs forest).drop k) need⟩)
        ms (.success (.of ())) pf := by simpa only [hcut] using hm
    have hpairs := MatchResulttypeDecision.match_pairs_of_resulttype_success c _ need ms pf hr htable hn hm'
    rw [houtputs]
    exact (MatchResulttypeDecision.match_pairs_iff_resulttype c _ need n hr htable hn).1 hpairs
  have hinstr : ∀ stack n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c (.NoEllipses,stack++outputs (forest.drop k)) i⟩)
      n (.success (.of (effect need u))) n := by
    intro stack n
    rw [houtputs]
    apply original_instruction_suffix c ((outputs forest).take k) ((outputs forest).drop k)
      stack i (effect need u) start finish n hs
    · simpa only [List.take_append_drop] using hi
    · simpa [effect,List.length_drop,outputs,k,Nat.sub_sub_self hlenf] using Nat.le_refl need.length
  intro t ht
  simp only [attach,List.mem_append,List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact hf t (List.mem_of_mem_take ht)
  · exact Good.node i u (forest.drop k) need hs hinstr hmatch
      (fun t ht => hf t (List.mem_of_mem_drop ht))

#print axioms attach_good
end properties.wasm_module_ok.ConstructiveConstTreeStep
