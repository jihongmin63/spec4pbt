import properties.wasm_module_ok.ConstructiveBodyFunctionMembers
import properties.wasm_module_ok.ConstructiveBodyFunctionOriginal
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyFunctionMetadata ConstructiveBodyEnvironment ConstructiveBodyFunctionProductions ConstructiveBodyProductionCoverage

 theorem from_production (c : context) (stack : inferresulttype) (ps : List (ConstructiveBodyProductions.Production c stack))
    (p : ConstructiveBodyProductions.Production c stack) (i : instr) (effect : inferinstrtype) (n finish : Nat)
    (hp : p∈ps) (hi : Produces p i)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩) n (.success (.of effect)) finish) :
    Covers ps i effect ∧ finish=n := by
  obtain ⟨v,hv,he⟩ := hi
  have hs := v.property n
  rw [he] at hs
  obtain ⟨heff,hn⟩ := ConstructiveBodyOperatorCalls.effect_unique c stack i p.effect effect n finish hs h
  exact ⟨⟨p,hp,heff.symm,⟨v,hv,he⟩⟩,hn⟩

theorem direct_produces (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS) :
    Produces (direct c stack env sig) (.CALL sig.entry.index) := by
  unfold Produces direct ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem direct_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.CALL x) effect ∧ finish=n := by
  obtain ⟨sig,hi⟩ := ConstructiveBodyFunctionOriginal.direct c stack x effect n finish h
  apply from_production c stack (all c stack env) (direct c stack env sig) _ effect n finish
    (ConstructiveBodyFunctionMembers.direct_mem c stack env sig) _ h
  simpa [hi] using direct_produces c stack env sig

theorem reference_produces (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES) :
    Produces (reference c stack env sig) (.CALL_REF sig.entry.index) := by
  unfold Produces reference ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem reference_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL_REF x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.CALL_REF x) effect ∧ finish=n := by
  obtain ⟨sig,hi⟩ := ConstructiveBodyFunctionOriginal.reference c stack x effect n finish h
  apply from_production c stack (all c stack env) (reference c stack env sig) _ effect n finish
    (ConstructiveBodyFunctionMembers.reference_mem c stack env sig) _ h
  simpa [hi] using reference_produces c stack env sig

theorem indirect_produces (c : context) (stack : inferresulttype) (env : Env c) (tab : FunctionTable c) (sig : Signature c.TYPES) :
    Produces (indirect c stack env tab sig) (.CALL_INDIRECT tab.index sig.entry.index) := by
  unfold Produces indirect ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem indirect_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CALL_INDIRECT x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.CALL_INDIRECT x y) effect ∧ finish=n := by
  obtain ⟨tab,sig,hx,hi⟩ := ConstructiveBodyFunctionOriginal.indirect c stack env x y effect n finish h
  apply from_production c stack (all c stack env) (indirect c stack env tab sig) _ effect n finish
    (ConstructiveBodyFunctionMembers.indirect_mem c stack env tab sig) _ h
  simpa [hi,hx] using indirect_produces c stack env tab sig

theorem returnDirect_produces (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    Produces (returnDirect c stack env sig hm) (.RETURN_CALL sig.entry.index) := by
  unfold Produces returnDirect ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem returnDirect_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.RETURN_CALL x) effect ∧ finish=n := by
  obtain ⟨sig,hi,hm⟩ := ConstructiveBodyFunctionOriginal.returnDirect c stack env x effect n finish h
  apply from_production c stack (all c stack env) (returnDirect c stack env sig hm) _ effect n finish
    (ConstructiveBodyFunctionMembers.returnDirect_mem c stack env sig hm) _ h
  simpa [hi] using returnDirect_produces c stack env sig hm

theorem returnReference_produces (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    Produces (returnReference c stack env sig hm) (.RETURN_CALL_REF sig.entry.index) := by
  unfold Produces returnReference ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem returnReference_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL_REF x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.RETURN_CALL_REF x) effect ∧ finish=n := by
  obtain ⟨sig,hi,hm⟩ := ConstructiveBodyFunctionOriginal.returnReference c stack env x effect n finish h
  apply from_production c stack (all c stack env) (returnReference c stack env sig hm) _ effect n finish
    (ConstructiveBodyFunctionMembers.returnReference_mem c stack env sig hm) _ h
  simpa [hi] using returnReference_produces c stack env sig hm

theorem returnIndirect_produces (c : context) (stack : inferresulttype) (env : Env c) (tab : FunctionTable c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    Produces (returnIndirect c stack env tab sig hm) (.RETURN_CALL_INDIRECT tab.index sig.entry.index) := by
  unfold Produces returnIndirect ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem returnIndirect_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.RETURN_CALL_INDIRECT x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.RETURN_CALL_INDIRECT x y) effect ∧ finish=n := by
  obtain ⟨tab,sig,hx,hi,hm⟩ := ConstructiveBodyFunctionOriginal.returnIndirect c stack env x y effect n finish h
  apply from_production c stack (all c stack env) (returnIndirect c stack env tab sig hm) _ effect n finish
    (ConstructiveBodyFunctionMembers.returnIndirect_mem c stack env tab sig hm) _ h
  simpa [hi,hx] using returnIndirect_produces c stack env tab sig hm

theorem throwTag_produces (c : context) (stack : inferresulttype) (env : Env c) (tag : ConstructiveBodyTagMetadata.Tag c) :
    Produces (throwTag c stack env tag) (.THROW tag.index) := by
  unfold Produces throwTag ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem throwTag_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.THROW x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.THROW x) effect ∧ finish=n := by
  obtain ⟨tag,hi⟩ := ConstructiveBodyFunctionOriginal.throwTag c stack x effect n finish h
  apply from_production c stack (all c stack env) (throwTag c stack env tag) _ effect n finish
    (ConstructiveBodyFunctionMembers.throwTag_mem c stack env tag) _ h
  simpa [hi] using throwTag_produces c stack env tag

#print axioms returnIndirect_original
#print axioms throwTag_original
end properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
