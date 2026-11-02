import properties.wasm_module_ok.CandidateUniverseReady
import properties.wasm_module_ok.FuncsValidation
import properties.wasm_module_ok.GlobaltypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenanceSteps

theorem in_table_val_of_types_eq
    (c out : SpecTec.context) (t : SpecTec.valtype)
    (hTypes : out.TYPES = c.TYPES)
    (h : CandidateValMatch.InTableVal c t) :
    CandidateValMatch.InTableVal out t := by
  intro ht hmem
  cases h ht hmem with
  | base heap hbase =>
      exact CandidateHeapMatch.InTable.base ht hbase
  | definition p dt hget =>
      exact CandidateHeapMatch.InTable.definition p dt
        (by simpa [hTypes] using hget)
  | static p dt hget =>
      exact CandidateHeapMatch.InTable.static p dt
        (by simpa [hTypes] using hget)

theorem empty_fields (c : SpecTec.context)
    (hf : c.FUNCS = []) (hg : c.GLOBALS = []) :
    CandidateUniverseReady.Provenance c := by
  constructor
  · intro dt h
    simp [hf] at h
  · intro gt h
    simp [hg] at h

theorem append_func (c : SpecTec.context)
    (dt : SpecTec.deftype)
    (hprov : CandidateUniverseReady.Provenance c)
    (hdt : dt ∈ c.TYPES) :
    CandidateUniverseReady.Provenance
      { c with FUNCS := c.FUNCS ++ [dt] } := by
  constructor
  · intro dt' h
    rcases List.mem_append.mp h with hold | hnew
    · exact hprov.funcs dt' hold
    · simp at hnew
      subst dt'
      exact hdt
  · intro gt h
    exact in_table_val_of_types_eq c _ _ rfl (hprov.globals gt h)

theorem append_valid_global (c : SpecTec.context)
    (gt : SpecTec.globaltype)
    (hprov : CandidateUniverseReady.Provenance c)
    (hvalid : GlobaltypeValidation.globaltypeValid c gt = true) :
    CandidateUniverseReady.Provenance
      { c with GLOBALS := c.GLOBALS ++ [gt] } := by
  constructor
  · intro dt h
    exact hprov.funcs dt h
  · intro gt' h
    rcases List.mem_append.mp h with hold | hnew
    · exact in_table_val_of_types_eq c _ _ rfl
        (hprov.globals gt' hold)
    · simp at hnew
      subst gt'
      cases gt with
      | GlobalT mutation t =>
          exact in_table_val_of_types_eq c _ _ rfl
            (CandidateValMembership.valid_candidate_in_table c t
              ((FiniteValidTypes.validCandidates_spec c t).2
                (by simpa [GlobaltypeValidation.globaltypeValid] using hvalid)))

theorem func_decl_result_provenance
    (c out : SpecTec.context) (f : SpecTec.func)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : FuncDeclValidation.funcDeclResult c f = some out) :
    CandidateUniverseReady.Provenance out := by
  cases hget : c.TYPES[f.FTYPE]? with
  | none => simp [FuncDeclValidation.funcDeclResult, hget] at h
  | some dt =>
      cases hft : UnrollInterface.deftypeFunctype dt with
      | none =>
          simp [FuncDeclValidation.funcDeclResult, hget, hft] at h
      | some ft =>
          simp [FuncDeclValidation.funcDeclResult, hget, hft] at h
          cases h
          exact append_func c dt hprov (List.mem_of_getElem? hget)

theorem funcs_result_provenance
    (c out : SpecTec.context) (fs : List SpecTec.func)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : FuncsValidation.funcsResult c fs = some out) :
    CandidateUniverseReady.Provenance out := by
  induction fs generalizing c out with
  | nil =>
      simp [FuncsValidation.funcsResult] at h
      cases h
      exact hprov
  | cons f fs ih =>
      cases hhead : FuncDeclValidation.funcDeclResult c f with
      | none => simp [FuncsValidation.funcsResult, hhead] at h
      | some next =>
          have htail : FuncsValidation.funcsResult next fs = some out := by
            simpa [FuncsValidation.funcsResult, hhead] using h
          exact ih next out
            (func_decl_result_provenance c next f hprov hhead) htail

end properties.wasm_module_ok.CandidateProvenanceSteps
