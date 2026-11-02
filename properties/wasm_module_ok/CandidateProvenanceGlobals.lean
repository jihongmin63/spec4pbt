import properties.wasm_module_ok.CandidateProvenanceSteps
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenanceGlobals

theorem global_ok_provenance
    (c out : SpecTec.context) (g : SpecTec.global)
    (start finish : Nat)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Global_ok c g⟩)
      start (.success (.of out)) finish) :
    CandidateUniverseReady.Provenance out := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Global_ok_clauses c g))
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hclause =>
          cases htype : g.GTYPE with
          | GlobalT mutation t =>
              unfold SpecTec.«Global_ok:clause:0» at hclause
              rw [htype] at hclause
              cases hclause with
              | bind_success hgt htail =>
                  cases htail with
                  | bind_success _ hpure =>
                      cases hpure with
                      | pure =>
                          have hvalid :
                              GlobaltypeValidation.globaltypeValid c
                                (.GlobalT mutation t) = true :=
                            ((GlobaltypeValidation.globaltype_success_iff_valid
                              c (.GlobalT mutation t) start _).mp hgt).1
                          exact CandidateProvenanceSteps.append_valid_global
                            c (.GlobalT mutation t) hprov hvalid
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem globals_ok_provenance
    (c out : SpecTec.context) (gs : List SpecTec.global)
    (start finish : Nat)
    (hprov : CandidateUniverseReady.Provenance c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Globals_ok c gs⟩)
      start (.success (.of out)) finish) :
    CandidateUniverseReady.Provenance out := by
  induction gs generalizing c out start finish with
  | nil =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Globals_ok:clause:0» c [])
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Globals_ok:clause:1» c []]))
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Globals_ok:clause:0» at hfirst
              cases hfirst with
              | bind_success hguard _ =>
                  cases hguard with
                  | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Globals_ok:clause:1» c [])
                  (fun _ => .unmatch))
                start (.success (.of out)) finish at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Globals_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success _ hpure =>
                      cases hpure with
                      | pure => exact hprov
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons g rest ih =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Globals_ok:clause:0» c (g :: rest))
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Globals_ok:clause:1» c (g :: rest)]))
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Globals_ok:clause:0» at hfirst
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
                                  exact ih next out middle finish
                                    (global_ok_provenance c next g start middle
                                      hprov hhead) hrest
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Globals_ok:clause:1» c (g :: rest))
                  (fun _ => .unmatch))
                start (.success (.of out)) finish at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Globals_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success hguard _ =>
                      cases hguard with
                      | guard_true hcond => simp at hcond
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

end properties.wasm_module_ok.CandidateProvenanceGlobals
