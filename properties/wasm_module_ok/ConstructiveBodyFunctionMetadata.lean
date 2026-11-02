import properties.wasm_module_ok.ConstructiveBodyLookup
import properties.wasm_module_ok.ConstructiveBodyTagCoverage
import properties.wasm_module_ok.FunctionTypeValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionMetadata
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyLookup

structure Signature (xs : List deftype) where
  entry : Entry xs
  inputs : List valtype
  outputs : List valtype
  expanded : UnrollInterface.expandResult entry.value=some (.DefFuncT (.FuncT inputs outputs))

-- Inspect existing context type metadata before choosing any instruction.
def signatures (xs : List deftype) : List (Signature xs) :=
  (entries xs).flatMap fun e =>
    match he : UnrollInterface.expandResult e.value with
    | some (.DefFuncT (.FuncT ins outs)) => [⟨e,ins,outs,he⟩]
    | _ => []

theorem complete (xs : List deftype) (sig : Signature xs) : sig∈signatures xs := by
  apply List.mem_flatMap.mpr
  refine ⟨sig.entry,ConstructiveBodyLookup.complete xs sig.entry,?_⟩
  split
  next ins outs he =>
    have hh : ins=sig.inputs ∧ outs=sig.outputs := by
      have hp := sig.expanded
      rw [he] at hp
      simpa using hp
    rcases hh with ⟨rfl,rfl⟩
    exact List.mem_singleton_self _
  next he => exact (he sig.inputs sig.outputs sig.expanded).elim

theorem Signature.backed {c : context} {xs : List deftype} (sig : Signature xs) (env : Env c)
    (hxs : ∀dt∈xs,dt∈c.TYPES) :
    ∀t∈sig.inputs++sig.outputs,CandidateValMatch.InTableVal c t := by
  obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp (hxs sig.entry.value sig.entry.mem)
  intro t ht heap hh
  exact ConstExtendedCandidateReady.expanded_source_in_table c env.nested x sig.entry.value
    (.DefFuncT (.FuncT sig.inputs sig.outputs)) hx sig.expanded heap
    (List.mem_flatMap.mpr ⟨t,ht,hh⟩)

theorem Signature.expand {xs : List deftype} (sig : Signature xs) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨strtype,SpecTecCall.«$expanddt» sig.entry.value⟩)
      n (.success (.of (strtype.DefFuncT (.FuncT sig.inputs sig.outputs)))) n :=
  (UnrollInterface.expanddt_success_iff_result _ _ n n).2 ⟨sig.expanded,rfl⟩

theorem Signature.functionType {c : context} (sig : Signature c.TYPES) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨functype,SpecTecCall.«$func_type» c sig.entry.index⟩)
      n (.success (.of (functype.FuncT sig.inputs sig.outputs))) n :=
  (FunctionTypeValidation.func_type_success_iff _ _ _ n n).2 ⟨sig.entry.value,sig.entry.lookup,sig.expand n⟩

#print axioms complete
#print axioms Signature.backed
end properties.wasm_module_ok.ConstructiveBodyFunctionMetadata
