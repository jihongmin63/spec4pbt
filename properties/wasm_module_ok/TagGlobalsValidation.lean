import properties.wasm_module_ok.MemGlobalsValidation
import properties.wasm_module_ok.TagsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.TagGlobalsValidation

theorem tag_decl_result_globals
    (c out : SpecTec.context) (t : SpecTec.tag)
    (h : TagsValidation.tagDeclResult c t = some out) :
    out.GLOBALS = c.GLOBALS := by
  cases hget : c.TYPES[t.TGTYPE]? with
  | none => simp [TagsValidation.tagDeclResult, hget] at h
  | some dt =>
      cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false =>
          simp [TagsValidation.tagDeclResult, hget, hv] at h
      | true =>
          simp [TagsValidation.tagDeclResult, hget, hv] at h
          cases h
          rfl

theorem tags_result_globals
    (c out : SpecTec.context) (ts : List SpecTec.tag)
    (h : TagsValidation.tagsResult c ts = some out) :
    out.GLOBALS = c.GLOBALS := by
  induction ts generalizing c out with
  | nil =>
      simp [TagsValidation.tagsResult] at h
      cases h
      rfl
  | cons t ts ih =>
      cases hhead : TagsValidation.tagDeclResult c t with
      | none =>
          simp [TagsValidation.tagsResult, hhead] at h
      | some c₁ =>
          have htail : TagsValidation.tagsResult c₁ ts = some out := by
            simpa [TagsValidation.tagsResult, hhead] using h
          exact (ih c₁ out htail).trans
            (tag_decl_result_globals c c₁ t hhead)

theorem tags_success_no_bot_candidate
    (c out : SpecTec.context) (ts : List SpecTec.tag)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Tags_ok c ts⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  have hresult :=
    (TagsValidation.tags_success_iff_result
      c ts out start fin).1 h |>.1
  intro hb
  obtain ⟨mutation, hm⟩ :=
    (ConstCandidateBot.bot_mem_candidate_iff out).1 hb
  rw [tags_result_globals c out ts hresult] at hm
  exact hinput
    ((ConstCandidateBot.bot_mem_candidate_iff c).2 ⟨mutation, hm⟩)

end properties.wasm_module_ok.TagGlobalsValidation
