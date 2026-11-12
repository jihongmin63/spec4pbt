import properties.wasm_module_ok.CandidateProvenanceGlobals
import properties.wasm_module_ok.ImportsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenanceImports

theorem of_relevant_fields_eq
    (c out : SpecTec.context)
    (hTypes : out.TYPES = c.TYPES)
    (hFuncs : out.FUNCS = c.FUNCS)
    (hGlobals : out.GLOBALS = c.GLOBALS)
    (hprov : CandidateUniverseReady.Provenance c) :
    CandidateUniverseReady.Provenance out := by
  constructor
  · intro dt h
    rw [hFuncs] at h
    simpa [hTypes] using hprov.funcs dt h
  · intro gt h
    rw [hGlobals] at h
    exact CandidateProvenanceSteps.in_table_val_of_types_eq
      c out _ hTypes (hprov.globals gt h)

theorem import_result_provenance
    (c out : SpecTec.context) (i : SpecTec.«import»)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : ImportValidation.importDeclResult c i = some out) :
    CandidateUniverseReady.Provenance out := by
  cases hdesc : i.IDESC with
  | FuncImport x =>
      cases hget : c.TYPES[x]? with
      | none =>
          simp [ImportValidation.importDeclResult, hdesc,
            ImportValidation.funcImportResult, hget] at h
      | some dt =>
          cases hft : UnrollInterface.deftypeFunctype dt with
          | none =>
              simp [ImportValidation.importDeclResult, hdesc,
                ImportValidation.funcImportResult, hget, hft] at h
          | some ft =>
              simp [ImportValidation.importDeclResult, hdesc,
                ImportValidation.funcImportResult, hget, hft] at h
              cases h
              exact CandidateProvenanceSteps.append_func c dt hprov
                (List.mem_of_getElem? hget)
  | GlobalImport gt =>
      cases hv : GlobaltypeValidation.globaltypeValid c gt with
      | false =>
          simp [ImportValidation.importDeclResult, hdesc, hv] at h
      | true =>
          simp [ImportValidation.importDeclResult, hdesc, hv] at h
          cases h
          exact CandidateProvenanceSteps.append_valid_global c gt hprov hv
  | TableImport tt =>
      cases hv : TabletypeValidation.tabletypeValid c tt with
      | false => simp [ImportValidation.importDeclResult, hdesc, hv] at h
      | true =>
          simp [ImportValidation.importDeclResult, hdesc, hv] at h
          cases h
          exact of_relevant_fields_eq c _ rfl rfl rfl hprov
  | MemImport mt =>
      cases hv : MemtypeValidation.memtypeValid mt with
      | false => simp [ImportValidation.importDeclResult, hdesc, hv] at h
      | true =>
          simp [ImportValidation.importDeclResult, hdesc, hv] at h
          cases h
          exact of_relevant_fields_eq c _ rfl rfl rfl hprov
  | TagImport x =>
      cases hget : c.TYPES[x]? with
      | none =>
          simp [ImportValidation.importDeclResult, hdesc,
            ImportValidation.tagImportResult, hget] at h
      | some dt =>
          cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
          | false =>
              simp [ImportValidation.importDeclResult, hdesc,
                ImportValidation.tagImportResult, hget, hv] at h
          | true =>
              simp [ImportValidation.importDeclResult, hdesc,
                ImportValidation.tagImportResult, hget, hv] at h
              cases h
              exact of_relevant_fields_eq c _ rfl rfl rfl hprov

theorem imports_result_provenance
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : ImportsValidation.importsResult c is = some out) :
    CandidateUniverseReady.Provenance out := by
  induction is generalizing c out with
  | nil =>
      simp [ImportsValidation.importsResult] at h
      cases h
      exact hprov
  | cons i is ih =>
      cases hhead : ImportValidation.importDeclResult c i with
      | none => simp [ImportsValidation.importsResult, hhead] at h
      | some next =>
          have htail : ImportsValidation.importsResult next is = some out := by
            simpa [ImportsValidation.importsResult, hhead] using h
          exact ih next out
            (import_result_provenance c next i hprov hhead) htail

theorem imports_ok_provenance
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (start finish : Nat)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok c is⟩)
      start (.success (.of out)) finish) :
    CandidateUniverseReady.Provenance out := by
  exact imports_result_provenance c out is hprov
    ((ImportsValidation.imports_success_iff_result c is out start finish).mp h).1

end properties.wasm_module_ok.CandidateProvenanceImports
