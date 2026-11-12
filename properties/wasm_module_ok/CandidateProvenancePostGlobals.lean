import properties.wasm_module_ok.CandidateProvenancePreGlobals
import properties.wasm_module_ok.TagGlobalsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenancePostGlobals

theorem tag_result_funcs
    (c out : SpecTec.context) (t : SpecTec.tag)
    (h : TagsValidation.tagDeclResult c t = some out) :
    out.FUNCS = c.FUNCS := by
  cases hget : c.TYPES[t.TGTYPE]? with
  | none => simp [TagsValidation.tagDeclResult, hget] at h
  | some dt =>
      cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false => simp [TagsValidation.tagDeclResult, hget, hv] at h
      | true =>
          simp [TagsValidation.tagDeclResult, hget, hv] at h
          cases h
          rfl

theorem tags_result_funcs
    (c out : SpecTec.context) (ts : List SpecTec.tag)
    (h : TagsValidation.tagsResult c ts = some out) :
    out.FUNCS = c.FUNCS := by
  induction ts generalizing c out with
  | nil =>
      simp [TagsValidation.tagsResult] at h
      cases h
      rfl
  | cons t ts ih =>
      cases hhead : TagsValidation.tagDeclResult c t with
      | none => simp [TagsValidation.tagsResult, hhead] at h
      | some next =>
          have htail : TagsValidation.tagsResult next ts = some out := by
            simpa [TagsValidation.tagsResult, hhead] using h
          exact (ih next out htail).trans
            (tag_result_funcs c next t hhead)

theorem trace_globals_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c5 := by
  exact CandidateProvenanceGlobals.globals_ok_provenance
    tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8
    (CandidateProvenancePreGlobals.trace_mems_provenance m tr)
    tr.globals_ok

theorem trace_tags_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c6 := by
  have hresult :=
    ((TagsValidation.tags_success_iff_result
      tr.c5 m.TAGS tr.c6 tr.n8 tr.n9).mp tr.tags_ok).1
  exact CandidateProvenanceImports.of_relevant_fields_eq tr.c5 tr.c6
    (ContextTypesValidation.tags_types tr.c5 tr.c6 m.TAGS hresult)
    (tags_result_funcs tr.c5 tr.c6 m.TAGS hresult)
    (TagGlobalsValidation.tags_result_globals tr.c5 tr.c6 m.TAGS hresult)
    (trace_globals_provenance m tr)

end properties.wasm_module_ok.CandidateProvenancePostGlobals
