import properties.wasm_module_ok.ConstructiveModuleEnvironment
import properties.wasm_module_ok.ConstructiveTypes
import properties.wasm_module_not_ok.InitialContextValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleTypesEnvironment
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

/-- Pure proof transport: the original type stage changes only TYPES. -/
theorem candidate_frame (c out : context) (sts : List SpecTec.subtype)
    (h : CandidateRectypeTable.candidateContext c sts=some out) : out={c with TYPES:=out.TYPES} := by
  cases ht : CandidateRectypeTable.transformed c sts with
  | none => simp [CandidateRectypeTable.candidateContext,ht] at h
  | some rt =>
    simp only [CandidateRectypeTable.candidateContext,ht,Option.map_some,Option.some.injEq] at h
    rw [←h]

theorem types_frame (c out : context) (ts : List SpecTec.type)
    (h : CandidateTypesDecision.typesResult c ts=some out) : out={c with TYPES:=out.TYPES} := by
  induction ts generalizing c with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases t with | RecT sts =>
      cases hp : CandidateRectypeDecision.rectypePasses c sts with
      | false => simp [CandidateTypesDecision.typesResult,hp] at h
      | true =>
        cases hc : CandidateRectypeTable.candidateContext c sts with
        | none => simp [CandidateTypesDecision.typesResult,hp,hc] at h
        | some next =>
          have ht : CandidateTypesDecision.typesResult next ts=some out := by
            simpa only [CandidateTypesDecision.typesResult,hp,ite_true,hc,Option.bind_some] using h
          calc
            out={next with TYPES:=out.TYPES} := ih next ht
            _={c with TYPES:=out.TYPES} := by rw [candidate_frame c next sts hc]

def initial (refs : SpecTec.free) : context :=
  {properties.wasm_module_not_ok.Rejection.emptyContext with REFS:=refs}

/-- Every arbitrary constructive Types result establishes its complete static
entry environment; no validity of a future module is used. -/
theorem generated (refs : SpecTec.free) (out : ConstructiveTypes.Result (initial refs)) : Env out.after := by
  have hv := out.state.validated
  have hf := types_frame (initial refs) out.after out.types
    (CandidateTypesDecision.types_result_of_success _ _ _ 0 0 (.seed _ rfl) (out.correct 0))
  have hfun : out.after.FUNCS=[] := congrArg context.FUNCS hf
  have hglobal : out.after.GLOBALS=[] := congrArg context.GLOBALS hf
  have hlocal : out.after.LOCALS=[] := congrArg context.LOCALS hf
  have hlabel : out.after.LABELS=[] := congrArg context.LABELS hf
  have hresult : out.after.RESULTS=[] := congrArg context.RESULTS hf
  have htable : out.after.TABLES=[] := congrArg context.TABLES hf
  have helem : out.after.ELEMS=[] := congrArg context.ELEMS hf
  have htag : out.after.TAGS=[] := congrArg context.TAGS hf
  refine ⟨CandidateTypeReady.validated_types_ready _ hv,⟨?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · intro dt hm; simp only [hfun,List.not_mem_nil] at hm
  · intro gt hm; simp only [hglobal,List.not_mem_nil] at hm
  · exact (CandidateNestedReady.nestedTableReady_true_iff _).2
      (fun p hp => ValidatedNestedReferences.validated_type_unrolled_nested_references _ p hv hp)
  · intro ini t hm; simp only [hlocal,List.not_mem_nil] at hm
  · intro ts hm; simp only [hlabel,List.not_mem_nil] at hm
  · intro t hm; simp only [hresult,List.not_mem_nil] at hm
  · intro addr lim rt hm; simp only [htable,List.not_mem_nil] at hm
  · intro rt hm; simp only [helem,List.not_mem_nil] at hm
  · intro dt hm; simp only [htag,List.not_mem_nil] at hm

#print axioms generated
end properties.wasm_module_ok.ConstructiveModuleTypesEnvironment
