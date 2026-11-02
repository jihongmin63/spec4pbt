import properties.wasm_module_ok.CandidateReftypeMatch
import properties.wasm_module_ok.TablesDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.TableProvenance

/-- Every table reference carried by this context has a heap form supported
by the exact ready-table matcher. -/
def Provenance (c : SpecTec.context) : Prop :=
  ∀ (addr : SpecTec.addrtype) (lim : SpecTec.limits)
    (rt : SpecTec.reftype),
    SpecTec.tabletype.TableT addr lim rt ∈ c.TABLES →
      CandidateValMatch.InTableVal c (.RefT rt)

theorem empty (c : SpecTec.context) (h : c.TABLES = []) :
    Provenance c := by
  intro addr lim rt hmem
  simp [h] at hmem

theorem of_fields_eq (c out : SpecTec.context)
    (hTypes : out.TYPES = c.TYPES)
    (hTables : out.TABLES = c.TABLES)
    (hprov : Provenance c) : Provenance out := by
  intro addr lim rt hmem
  exact CandidateProvenanceSteps.in_table_val_of_types_eq c out _ hTypes
    (hprov addr lim rt (by simpa [hTables] using hmem))

theorem append_valid_tabletype (c : SpecTec.context)
    (addr : SpecTec.addrtype) (lim : SpecTec.limits)
    (rt : SpecTec.reftype)
    (hprov : Provenance c)
    (hvalid : TabletypeValidation.tabletypeValid c
      (.TableT addr lim rt) = true) :
    Provenance {c with TABLES :=
      c.TABLES ++ [.TableT addr lim rt]} := by
  intro addr' lim' rt' hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact CandidateProvenanceSteps.in_table_val_of_types_eq c _ _ rfl
      (hprov addr' lim' rt' hold)
  · simp only [List.mem_singleton] at hnew
    cases hnew
    have hcall :=
      (TabletypeValidation.tabletype_success_iff_valid
        c (.TableT addr lim rt) 0 0).2 ⟨hvalid, rfl⟩
    exact CandidateProvenanceSteps.in_table_val_of_types_eq c _ _ rfl
      (ConstValidatedTarget.tabletype_target_in_extended_and_table
        c addr lim rt 0 0 hcall).2

theorem table_result_provenance (c out : SpecTec.context)
    (tab : SpecTec.table) (hprov : Provenance c)
    (hresult : TableDecision.tableResult c tab = some out) :
    Provenance out := by
  obtain ⟨hvalid, hout⟩ :=
    (TableDecision.table_result_iff_valid c out tab).1 hresult
  cases tab with
  | mk tt init =>
    cases tt with
    | TableT addr lim rt =>
      subst out
      have htype : TabletypeValidation.tabletypeValid c
          (.TableT addr lim rt) = true := by
        have hparts :
            TabletypeValidation.tabletypeValid c (.TableT addr lim rt) = true ∧
              ConstExpressionDecision.constantExpressionResult c
                (.RefT rt) init = true := by
          simpa only [TableDecision.tableValid, Bool.and_eq_true] using hvalid
        exact hparts.1
      exact append_valid_tabletype c addr lim rt hprov htype

theorem tables_result_provenance (c out : SpecTec.context)
    (tabs : List SpecTec.table) (hprov : Provenance c)
    (hresult : TablesDecision.tablesResult c tabs = some out) :
    Provenance out := by
  induction tabs generalizing c out with
  | nil =>
    simp [TablesDecision.tablesResult] at hresult
    cases hresult
    exact hprov
  | cons tab rest ih =>
    cases hhead : TableDecision.tableResult c tab with
    | none => simp [TablesDecision.tablesResult, hhead] at hresult
    | some next =>
      have htail : TablesDecision.tablesResult next rest = some out := by
        simpa [TablesDecision.tablesResult, hhead] using hresult
      exact ih next out
        (table_result_provenance c next tab hprov hhead) htail

theorem tables_ok_provenance (c out : SpecTec.context)
    (tabs : List SpecTec.table) (start finish : Nat)
    (hprov : Provenance c)
    (hready : CandidateTypeReady.Ready c)
    (hcandidates : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Tables_ok c tabs⟩)
      start (.success (.of out)) finish) : Provenance out := by
  exact tables_result_provenance c out tabs hprov
    ((TablesDecision.tables_result_iff_call c out tabs start finish
      hready hcandidates hnested).2 hcall).1

theorem import_result_provenance (c out : SpecTec.context)
    (i : SpecTec.«import») (hprov : Provenance c)
    (hresult : ImportValidation.importDeclResult c i = some out) :
    Provenance out := by
  cases hdesc : i.IDESC with
  | FuncImport x =>
    cases hget : c.TYPES[x]? with
    | none =>
        simp [ImportValidation.importDeclResult, hdesc,
          ImportValidation.funcImportResult, hget] at hresult
    | some dt =>
        cases hft : UnrollInterface.deftypeFunctype dt with
        | none =>
            simp [ImportValidation.importDeclResult, hdesc,
              ImportValidation.funcImportResult, hget, hft] at hresult
        | some ft =>
            simp [ImportValidation.importDeclResult, hdesc,
              ImportValidation.funcImportResult, hget, hft] at hresult
            cases hresult
            exact of_fields_eq c _ rfl rfl hprov
  | GlobalImport gt =>
    cases hv : GlobaltypeValidation.globaltypeValid c gt with
    | false =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
    | true =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
        cases hresult
        exact of_fields_eq c _ rfl rfl hprov
  | TableImport tt =>
    cases hv : TabletypeValidation.tabletypeValid c tt with
    | false =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
    | true =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
        cases hresult
        cases tt with
        | TableT addr lim rt =>
            exact append_valid_tabletype c addr lim rt hprov hv
  | MemImport mt =>
    cases hv : MemtypeValidation.memtypeValid mt with
    | false =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
    | true =>
        simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
        cases hresult
        exact of_fields_eq c _ rfl rfl hprov
  | TagImport x =>
    cases hget : c.TYPES[x]? with
    | none =>
        simp [ImportValidation.importDeclResult, hdesc,
          ImportValidation.tagImportResult, hget] at hresult
    | some dt =>
        cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
        | false =>
            simp [ImportValidation.importDeclResult, hdesc,
              ImportValidation.tagImportResult, hget, hv] at hresult
        | true =>
            simp [ImportValidation.importDeclResult, hdesc,
              ImportValidation.tagImportResult, hget, hv] at hresult
            cases hresult
            exact of_fields_eq c _ rfl rfl hprov

theorem imports_result_provenance (c out : SpecTec.context)
    (is : List SpecTec.«import») (hprov : Provenance c)
    (hresult : ImportsValidation.importsResult c is = some out) :
    Provenance out := by
  induction is generalizing c out with
  | nil =>
    simp [ImportsValidation.importsResult] at hresult
    cases hresult
    exact hprov
  | cons i rest ih =>
    cases hhead : ImportValidation.importDeclResult c i with
    | none => simp [ImportsValidation.importsResult, hhead] at hresult
    | some next =>
      have htail : ImportsValidation.importsResult next rest = some out := by
        simpa [ImportsValidation.importsResult, hhead] using hresult
      exact ih next out
        (import_result_provenance c next i hprov hhead) htail

theorem imports_ok_provenance (c out : SpecTec.context)
    (is : List SpecTec.«import») (start finish : Nat)
    (hprov : Provenance c)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Imports_ok c is⟩)
      start (.success (.of out)) finish) : Provenance out := by
  exact imports_result_provenance c out is hprov
    ((ImportsValidation.imports_success_iff_result
      c is out start finish).mp hcall).1

end properties.wasm_module_ok.TableProvenance
