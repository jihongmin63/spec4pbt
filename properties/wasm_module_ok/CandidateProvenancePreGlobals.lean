import properties.wasm_module_ok.CandidateProvenanceSeed
import properties.wasm_module_ok.DeclarationTypesValidation
import properties.wasm_module_ok.ContextTypesValidation
import properties.wasm_module_ok.MemGlobalsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenancePreGlobals

theorem table_ok_funcs
    (c out : SpecTec.context) (t : SpecTec.table)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Table_ok c t⟩)
      start (.success (.of out)) finish) :
    out.FUNCS = c.FUNCS := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Table_ok_clauses c t))
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hclause =>
          unfold SpecTec.«Table_ok:clause:0» at hclause
          cases hclause with
          | bind_success _ htail =>
              cases htail with
              | bind_success _ hpure =>
                  cases hpure with
                  | pure => rfl
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem tables_ok_funcs
    (c out : SpecTec.context) (ts : List SpecTec.table)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c ts⟩)
      start (.success (.of out)) finish) :
    out.FUNCS = c.FUNCS := by
  induction ts generalizing c out start finish with
  | nil =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Tables_ok:clause:0» c [])
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Tables_ok:clause:1» c []]))
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Tables_ok:clause:0» at hfirst
              cases hfirst with
              | bind_success hguard _ =>
                  cases hguard with
                  | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Tables_ok:clause:1» c [])
                  (fun _ => .unmatch))
                start (.success (.of out)) finish at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Tables_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success _ hpure =>
                      cases hpure with
                      | pure => rfl
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons t rest ih =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Tables_ok:clause:0» c (t :: rest))
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Tables_ok:clause:1» c (t :: rest)]))
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Tables_ok:clause:0» at hfirst
              cases hfirst with
              | bind_success hguard htail =>
                  cases hguard with
                  | guard_true _ =>
                      cases htail with
                      | bind_success hhead htail =>
                          rename_i middle next
                          cases htail with
                          | bind_success hrest hpure =>
                              cases hpure with
                              | pure =>
                                  exact (ih next out middle finish hrest).trans
                                    (table_ok_funcs c next t start middle hhead)
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Tables_ok:clause:1» c (t :: rest))
                  (fun _ => .unmatch))
                start (.success (.of out)) finish at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Tables_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success hguard _ =>
                      cases hguard with
                      | guard_true hcond => simp at hcond
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem mems_result_funcs
    (c out : SpecTec.context) (ms : List SpecTec.memory)
    (h : MemsValidation.memsResult c ms = some out) :
    out.FUNCS = c.FUNCS := by
  induction ms generalizing c out with
  | nil =>
      simp [MemsValidation.memsResult] at h
      cases h
      rfl
  | cons m ms ih =>
      cases hhead : MemsValidation.memDeclResult c m with
      | none => simp [MemsValidation.memsResult, hhead] at h
      | some next =>
          have htail : MemsValidation.memsResult next ms = some out := by
            simpa [MemsValidation.memsResult, hhead] using h
          have hstep : next.FUNCS = c.FUNCS := by
            cases hv : MemtypeValidation.memtypeValid m.MTYPE with
            | false => simp [MemsValidation.memDeclResult, hv] at hhead
            | true =>
                simp [MemsValidation.memDeclResult, hv] at hhead
                cases hhead
                rfl
          exact (ih next out htail).trans hstep

theorem trace_tables_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c3 := by
  exact CandidateProvenanceImports.of_relevant_fields_eq tr.c2 tr.c3
    (DeclarationTypesValidation.tables_ok_types
      tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok)
    (tables_ok_funcs tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok)
    (TableGlobalsValidation.tables_ok_globals
      tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok)
    (CandidateProvenanceSeed.trace_funcs_provenance m tr)

theorem trace_mems_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c4 := by
  have hresult :=
    ((MemsValidation.mems_success_iff_result
      tr.c3 m.MEMS tr.c4 tr.n6 tr.n7).mp tr.mems_ok).1
  exact CandidateProvenanceImports.of_relevant_fields_eq tr.c3 tr.c4
    (ContextTypesValidation.mems_types tr.c3 tr.c4 m.MEMS hresult)
    (mems_result_funcs tr.c3 tr.c4 m.MEMS hresult)
    (MemGlobalsValidation.mems_result_globals tr.c3 tr.c4 m.MEMS hresult)
    (trace_tables_provenance m tr)

end properties.wasm_module_ok.CandidateProvenancePreGlobals
