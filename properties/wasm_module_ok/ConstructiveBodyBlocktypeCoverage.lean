import properties.wasm_module_ok.ConstructiveBodyBlocktypes
import properties.wasm_module_ok.ConstructiveBodyEnvironment
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBlocktypeCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyBlocktypes ConstructiveBodyEnvironment

theorem source_cases (c : context) (bt : blocktype) (result : instrtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨instrtype,Call.Blocktype_ok c bt⟩) start (.success (.of result)) finish) :
    finish=start ∧
      ((bt=.ValBlockType none ∧ result=.InstrT [] [] []) ∨
      (∃t,bt=.ValBlockType (some t) ∧ ValtypeValidation.valtypeValid c t=true ∧ result=.InstrT [] [t] []) ∨
      (∃x ins outs,bt=.VarBlockType x ∧ FunctionTypeValidation.funcTypeResult c x=some (.FuncT ins outs) ∧ result=.InstrT ins outs [])) := by
  cases h with | call h =>
   change SpecTecExecution.Eval SpecTec.Body
     (SpecTecExecution.tryClauses (SpecTec.Blocktype_ok_clauses c bt))
     start (.success (.of result)) finish at h
   obtain ⟨k,h⟩ := (properties.wasm_module_ok.Execution.tryClauses_success_iff _ _ _ _).1 h
   unfold SpecTec.Blocktype_ok_clauses at h
   rcases h with h|⟨_,h|⟨_,h|⟨_,h⟩⟩⟩
   · unfold SpecTec.«Blocktype_ok:clause:0» at h
     cases h with | bind_success hg hp =>
      cases hg with | guard_true he =>
       cases he
       cases hp
       exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
   · unfold SpecTec.«Blocktype_ok:clause:1» at h
     cases h with | bind_success hg h =>
      cases hg with | guard_true hg =>
       cases bt with
       | VarBlockType x => simp [SpecTec.«exec:match:blocktype:ValBlockType»] at hg
       | ValBlockType opt =>
         cases opt with
         | none =>
           cases h with | bind_success hg _ =>
            cases hg with | guard_true hg => cases hg
         | some t =>
           cases h with | bind_success hg h =>
            cases hg with | guard_true _ =>
             cases h with | bind_success hv hp =>
              cases_type Unit
              cases hp
              obtain ⟨hvalid,hcounter⟩ := (ValtypeValidation.valtype_success_iff_valid c t _ _).1 hv
              exact ⟨hcounter,Or.inr (Or.inl ⟨t,rfl,hvalid,rfl⟩)⟩
   · unfold SpecTec.«Blocktype_ok:clause:2» at h
     cases h with | bind_success hg h =>
      cases hg with | guard_true hg =>
       cases bt with
       | ValBlockType opt => simp [SpecTec.«exec:match:blocktype:VarBlockType»] at hg
       | VarBlockType x =>
         cases h with | bind_success hf hp =>
          rename_i ft
          cases ft with | FuncT ins outs =>
           cases hp
           obtain ⟨hresult,hcounter⟩ := (FunctionTypeValidation.func_type_success_iff_result c x (.FuncT ins outs) _ _).1 hf
           exact ⟨hcounter,Or.inr (Or.inr ⟨x,ins,outs,rfl,hresult,rfl⟩)⟩
   · cases h

theorem value_mem (c : context) (t : valtype) (ht : ValtypeValidation.valtypeValid c t=true) :
    value c t ht ∈ signatures c := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨⟨t,(FiniteValidTypes.validCandidates_spec c t).2 ht⟩,by simp,rfl⟩

theorem index_mem (c : context) (x : Nat) (ins outs : List valtype)
    (ht : FunctionTypeValidation.funcTypeResult c x=some (.FuncT ins outs)) :
    index c x ins outs ht ∈ signatures c := by
  have hx : x<c.TYPES.length := by
    cases he : c.TYPES[x]? with
    | none => simp [FunctionTypeValidation.funcTypeResult,he] at ht
    | some dt => exact (List.getElem?_eq_some_iff.mp he).1
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨x,hx⟩,by simp,?_⟩
  split
  next ins' outs' he =>
    have hh : ins'=ins ∧ outs'=outs := by simpa [he] using ht
    rcases hh with ⟨rfl,rfl⟩
    exact List.mem_singleton_self _
  next he => simp [he] at ht

theorem signatures_complete (c : context) (bt : blocktype) (result : instrtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨instrtype,Call.Blocktype_ok c bt⟩) start (.success (.of result)) finish) :
    ∃s∈signatures c,s.raw=bt ∧ result=.InstrT s.inputs s.outputs [] ∧ finish=start := by
  obtain ⟨hf,h⟩ := source_cases c bt result start finish h
  rcases h with ⟨rfl,rfl⟩|⟨t,rfl,ht,rfl⟩|⟨x,ins,outs,rfl,ht,rfl⟩
  · exact ⟨empty c,by simp [signatures],rfl,rfl,hf⟩
  · exact ⟨value c t ht,value_mem c t ht,rfl,rfl,hf⟩
  · exact ⟨index c x ins outs ht,index_mem c x ins outs ht,rfl,rfl,hf⟩

theorem function_backed (c : context) (hn : CandidateNestedReady.nestedTableReady c=true)
    (x : Nat) (ins outs : List valtype)
    (hf : FunctionTypeValidation.funcTypeResult c x=some (.FuncT ins outs)) :
    ∀t∈ins++outs,CandidateValMatch.InTableVal c t := by
  have he := (FunctionTypeValidation.func_type_success_iff_result c x (.FuncT ins outs) 0 0).2 ⟨hf,rfl⟩
  obtain ⟨dt,hget,he⟩ := (FunctionTypeValidation.func_type_success_iff c x (.FuncT ins outs) 0 0).1 he
  have hex := (UnrollInterface.expanddt_success_iff_result dt (.DefFuncT (.FuncT ins outs)) 0 0).1 he |>.1
  intro t ht heap hh
  exact ConstExtendedCandidateReady.expanded_source_in_table c hn x dt (.DefFuncT (.FuncT ins outs))
    hget hex heap (List.mem_flatMap.mpr ⟨t,ht,hh⟩)

theorem signature_backed (c : context) (env : Env c) (s : Signature c) :
    ∀t∈s.inputs++s.outputs,CandidateValMatch.InTableVal c t := by
  obtain ⟨_,h⟩ := source_cases c s.raw (.InstrT s.inputs s.outputs []) 0 0 (s.valid 0)
  rcases h with ⟨_,he⟩|⟨t,_,ht,he⟩|⟨x,ins,outs,_,ht,he⟩
  · injection he with hi ho
    simp [hi,ho]
  · injection he with hi ho
    rw [hi,ho]
    intro u hu
    have hu' : u=t := by simpa using hu
    subst u
    exact CandidateValMembership.valid_candidate_in_table c t ((FiniteValidTypes.validCandidates_spec c t).2 ht)
  · injection he with hi ho
    rw [hi,ho]
    exact function_backed c env.nested x ins outs ht

#print axioms signatures_complete
#print axioms signature_backed
end properties.wasm_module_ok.ConstructiveBodyBlocktypeCoverage
