import properties.wasm_module_ok.ConstructiveBodyMatchers
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTagMetadata
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

structure Tag (c : context) where
  index : Nat
  definition : deftype
  inputs : List valtype
  outputs : List valtype
  lookup : c.TAGS[index]?=some (.TagT definition)
  expanded : UnrollInterface.expandResult definition=some (.DefFuncT (.FuncT inputs outputs))

def tags (c : context) : List (Tag c) :=
  (List.finRange c.TAGS.length).flatMap fun x =>
    match ht : c.TAGS[x.val] with
    | .TagT dt =>
      match he : UnrollInterface.expandResult dt with
      | some (.DefFuncT (.FuncT ins outs)) =>
        [⟨x.val,dt,ins,outs,by simpa [ht] using (List.getElem?_eq_getElem (as:=c.TAGS) x.isLt),he⟩]
      | _ => []

theorem Tag.backed {c : context} (tag : Tag c) (env : Env c) :
    ∀t∈tag.inputs++tag.outputs,CandidateValMatch.InTableVal c t := by
  have hdt := env.tags tag.definition (List.mem_iff_getElem?.mpr ⟨tag.index,tag.lookup⟩)
  obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hdt
  intro t ht heap hh
  exact ConstExtendedCandidateReady.expanded_source_in_table c env.nested x tag.definition
    (.DefFuncT (.FuncT tag.inputs tag.outputs)) hx tag.expanded heap
    (List.mem_flatMap.mpr ⟨t,ht,hh⟩)

def exn : valtype := .RefT (.«% %» .NoNull .ExnHT)
theorem exn_backed (c : context) : CandidateValMatch.InTableVal c exn := by
  intro heap hm
  have he : heap=.ExnHT := by simpa [exn,ReadyMatchReachability.sourceValHeaptypes] using hm
  subst heap
  exact .base .ExnHT (by simp [HeaptypeValidation.baseHeaptypes])

def arguments {c : context} (tag : Tag c) (withRef : Bool) : List valtype :=
  tag.inputs ++ if withRef then [exn] else []

theorem arguments_backed {c : context} (tag : Tag c) (env : Env c) (withRef : Bool) :
    ∀t∈arguments tag withRef,CandidateValMatch.InTableVal c t := by
  intro t ht
  rcases List.mem_append.mp ht with hi|he
  · exact tag.backed env t (List.mem_append_left _ hi)
  · cases withRef with
    | false => cases he
    | true => have he' : t=exn := by simpa using he
              subst t; exact exn_backed c

#print axioms Tag.backed
end properties.wasm_module_ok.ConstructiveBodyTagMetadata
