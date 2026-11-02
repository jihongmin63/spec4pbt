import properties.wasm_module_ok.TableDecision
import properties.wasm_module_ok.CandidateProvenanceImports
import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.ConstTraceNestedReady
import properties.wasm_module_ok.EmptyStageValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.TablesDecision

def tablesResult (c : SpecTec.context) :
    List SpecTec.table → Option SpecTec.context
  | [] => some c
  | g :: rest =>
      (TableDecision.tableResult c g).bind fun next =>
        tablesResult next rest

theorem table_result_next_invariants
    (c next : SpecTec.context) (g : SpecTec.table)
    (hresult : TableDecision.tableResult c g = some next)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    CandidateTypeReady.Ready next ∧
      CandidateUniverseReady.Provenance next ∧
      CandidateNestedReady.nestedTableReady next = true := by
  have hout := (TableDecision.table_result_iff_valid c next g).1 hresult |>.2
  have htypes : next.TYPES = c.TYPES := by
    rw [hout]
  have hfuncs : next.FUNCS = c.FUNCS := by
    rw [hout]
  have hglobals : next.GLOBALS = c.GLOBALS := by
    rw [hout]
  exact ⟨CandidateProvenanceElemDataFuncs.ready_of_types_eq
      c next htypes hready,
    CandidateProvenanceImports.of_relevant_fields_eq
      c next htypes hfuncs hglobals hprov,
    (ConstTraceNestedReady.nested_table_ready_of_types_eq
      next c htypes).trans hnested⟩

theorem tables_nil_success_iff
    (c out : SpecTec.context) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c []⟩)
      start (.success (.of out)) finish ↔
    c = out ∧ finish = start := by
  constructor
  · intro hcall
    obtain ⟨hout, hfinish⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic hcall
        (EmptyStageValidation.tables_nil_total c start)
    exact ⟨by cases hout; rfl, hfinish⟩
  · rintro ⟨hout, hfinish⟩
    subst out
    subst finish
    exact EmptyStageValidation.tables_nil_total c start

theorem tables_cons_success_iff
    (c out : SpecTec.context) (g : SpecTec.table)
    (rest : List SpecTec.table) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Tables_ok c (g :: rest)⟩)
      start (.success (.of out)) finish ↔
    ∃ next : SpecTec.context, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Table_ok c g⟩)
        start (.success (.of next)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok next rest⟩)
        middle (.success (.of out)) finish := by
  constructor
  · intro hcall
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Tables_ok_clauses c (g :: rest)))
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
                | pure => exact ⟨next, middle, hhead, hrest⟩
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Tables_ok:clause:1» c (g :: rest)])
          start (.success (.of out)) finish at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Tables_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨next, middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Tables_ok_clauses c (g :: rest)))
      start (.success (.of out)) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Tables_ok:clause:0» c (g :: rest))
      start (.success (.of out)) finish
    unfold SpecTec.«Tables_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success hrest
    exact SpecTecExecution.Eval.pure out

theorem tables_result_iff_call
    (c out : SpecTec.context) (gs : List SpecTec.table)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    tablesResult c gs = some out ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c gs⟩)
        start (.success (.of out)) finish := by
  induction gs generalizing c out start finish with
  | nil =>
    simpa [tablesResult] using
      (tables_nil_success_iff c out start finish).symm
  | cons g rest ih =>
    constructor
    · rintro ⟨hresult, hfinish⟩
      cases hhead : TableDecision.tableResult c g with
      | none => simp [tablesResult, hhead] at hresult
      | some next =>
        have htail : tablesResult next rest = some out := by
          simpa [tablesResult, hhead] using hresult
        obtain ⟨hreadyNext, hprovNext, hnestedNext⟩ :=
          table_result_next_invariants c next g hhead
            hready hprov hnested
        subst finish
        apply (tables_cons_success_iff c out g rest start start).2
        refine ⟨next, start, ?_, ?_⟩
        · exact (TableDecision.table_result_iff_call c next g
            start start hready hprov hnested).1 ⟨hhead, rfl⟩
        · exact (ih next out start start
            hreadyNext hprovNext hnestedNext).1 ⟨htail, rfl⟩
    · intro hcall
      obtain ⟨next, middle, hhead, htail⟩ :=
        (tables_cons_success_iff c out g rest start finish).1 hcall
      obtain ⟨hheadResult, hmiddle⟩ :=
        (TableDecision.table_result_iff_call c next g
          start middle hready hprov hnested).2 hhead
      obtain ⟨hreadyNext, hprovNext, hnestedNext⟩ :=
        table_result_next_invariants c next g hheadResult
          hready hprov hnested
      obtain ⟨htailResult, hfinish⟩ :=
        (ih next out middle finish
          hreadyNext hprovNext hnestedNext).2 htail
      exact ⟨by simpa [tablesResult, hheadResult] using htailResult,
        hfinish.trans hmiddle⟩

end properties.wasm_module_ok.TablesDecision
