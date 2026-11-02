import properties.wasm_module_ok.ConstructiveBodyCatches
import properties.wasm_module_ok.ConstructiveBodyTagCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCatchCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyTagMetadata ConstructiveBodyCatches

theorem specific_mem (c : context) (env : Env c) (tag : Tag c) (withRef : Bool)
    (y : Fin c.LABELS.length)
    (hm : MatchResulttypeDecision.matchPairs c (arguments tag withRef) c.LABELS[y.val]=true) :
    specific c env tag withRef y hm ∈ handlers c env := by
  apply List.mem_flatMap.mpr
  refine ⟨y,by simp,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨tag,ConstructiveBodyTagCoverage.tags_complete c tag,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨withRef,by cases withRef <;> simp,?_⟩
  simp [hm]

theorem all_mem (c : context) (env : Env c) (withRef : Bool) (y : Fin c.LABELS.length)
    (hm : MatchResulttypeDecision.matchPairs c (if withRef then [exn] else []) c.LABELS[y.val]=true) :
    all c env withRef y hm ∈ handlers c env := by
  apply List.mem_flatMap.mpr
  refine ⟨y,by simp,?_⟩
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨withRef,by cases withRef <;> simp,?_⟩
  simp [hm]

abbrev Covers (c : context) (env : Env c) (raw : SpecTec.«catch») :=
  ∃h∈handlers c env,h.val=raw

theorem specific_covers (c : context) (env : Env c) (tag : Tag c) (withRef : Bool)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES (arguments tag withRef) target⟩)
      start (.success (.of true)) finish) :
    Covers c env (if withRef then .CatchRef tag.index y else .Catch tag.index y) := by
  have hm := (ConstructiveBodyMatchers.result_exact c (arguments tag withRef) target true start finish env.ready
    (arguments_backed tag env withRef) (env.labels target (List.mem_iff_getElem?.mpr ⟨y,hy⟩))).1 h |>.1.symm
  have hyl := (List.getElem?_eq_some_iff.mp hy).1
  have hget := (List.getElem?_eq_some_iff.mp hy).2
  have hm' : MatchResulttypeDecision.matchPairs c (arguments tag withRef) c.LABELS[y]=true := by simpa [hget] using hm
  refine ⟨specific c env tag withRef ⟨y,hyl⟩ hm',specific_mem c env tag withRef ⟨y,hyl⟩ hm',?_⟩
  cases withRef <;> rfl

theorem all_covers (c : context) (env : Env c) (withRef : Bool)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES (if withRef then [exn] else []) target⟩)
      start (.success (.of true)) finish) :
    Covers c env (if withRef then .CatchAllRef y else .CatchAll y) := by
  have hb : ∀t∈(if withRef then [exn] else []),CandidateValMatch.InTableVal c t := by
    cases withRef with
    | false => simp
    | true => intro t ht; have he : t=exn := by simpa using ht
              subst t; exact exn_backed c
  have hm := (ConstructiveBodyMatchers.result_exact c _ target true start finish env.ready hb
    (env.labels target (List.mem_iff_getElem?.mpr ⟨y,hy⟩))).1 h |>.1.symm
  have hyl := (List.getElem?_eq_some_iff.mp hy).1
  have hget := (List.getElem?_eq_some_iff.mp hy).2
  have hm' : MatchResulttypeDecision.matchPairs c (if withRef then [exn] else []) c.LABELS[y]=true := by simpa [hget] using hm
  refine ⟨all c env withRef ⟨y,hyl⟩ hm',all_mem c env withRef ⟨y,hyl⟩ hm',?_⟩
  cases withRef <;> rfl

#print axioms specific_covers
#print axioms all_covers
end properties.wasm_module_ok.ConstructiveBodyCatchCoverage
