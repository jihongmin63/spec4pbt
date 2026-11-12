import properties.wasm_module_ok.ConstructiveBodyTopMetadata
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTopCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyTopHeap ConstructiveBodyTopMetadata

theorem bot_unmatch (c : context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$top_of_heap_type» c.TYPES .BotHT⟩) n .unmatch n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$top_of_heap_type_clauses» c.TYPES .BotHT)) n .unmatch n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«sub:heaptype:heaptypeVar»]))
  exact SpecTecExecution.tryClauses_nil n

theorem not_bot (c : context) (heap top : heaptype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$top_of_heap_type» c.TYPES heap⟩) n (.success (.of top)) finish) : heap≠.BotHT := by
  intro he
  subst heap
  have hc := (properties.wasm_module_ok.Execution.eval_deterministic h (bot_unmatch c n)).1
  cases hc

theorem all_complete (c : context) (hr : CandidateTypeReady.Ready c) (heap : heaptype)
    (hv : HeaptypeValidation.heaptypeValid c heap=true) (hn : heap≠.BotHT) :
    ∃t∈all c,t.heap=heap := by
  rcases (HeaptypeValidation.heaptype_valid_iff c heap).1 hv with hb|⟨x,rfl,hx⟩
  · have hex : ∃top,(heap,top)∈basePairs := by
      cases heap <;> simp_all [HeaptypeValidation.baseHeaptypes,basePairs]
    obtain ⟨top,hp⟩ := hex
    exact ⟨base c (heap,top) hp,base_mem c (heap,top) hp,rfl⟩
  · let e : ConstructiveBodyLookup.Entry c.TYPES := ⟨x,c.TYPES[x],List.getElem?_eq_getElem hx⟩
    obtain ⟨s,he⟩ := shape_exists c hr e
    refine ⟨indexed c s,indexed_mem c s,?_⟩
    change heaptype.VarHT (.StatX s.entry.index)=_
    rw [he]

#print axioms all_complete
#print axioms not_bot
end properties.wasm_module_ok.ConstructiveBodyTopCoverage
