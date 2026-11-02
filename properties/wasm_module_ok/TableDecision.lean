import properties.wasm_module_ok.ConstExpressionDecision
import properties.wasm_module_ok.ConstValidatedTarget

set_option autoImplicit false

namespace properties.wasm_module_ok.TableDecision

def tableValid (c : SpecTec.context) (tab : SpecTec.table) : Bool :=
  match tab.TTYPE with
  | .TableT _ _ rt =>
      TabletypeValidation.tabletypeValid c tab.TTYPE &&
        ConstExpressionDecision.constantExpressionResult c (.RefT rt) tab.TINIT

def tableResult (c : SpecTec.context) (tab : SpecTec.table) :
    Option SpecTec.context :=
  if tableValid c tab then
    some {c with TABLES := c.TABLES ++ [tab.TTYPE]}
  else none

theorem table_result_iff_valid
    (c out : SpecTec.context) (tab : SpecTec.table) :
    tableResult c tab = some out ↔
      tableValid c tab = true ∧
        out = {c with TABLES := c.TABLES ++ [tab.TTYPE]} := by
  cases hvalid : tableValid c tab <;>
    simp [tableResult, hvalid, eq_comm]

theorem table_result_iff_call
    (c out : SpecTec.context) (tab : SpecTec.table)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    tableResult c tab = some out ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Table_ok c tab⟩)
        start (.success (.of out)) finish := by
  cases tab with
  | mk tt init =>
    cases tt with
    | TableT addr lim rt =>
      constructor
      · rintro ⟨hresult, hfinish⟩
        obtain ⟨hvalid, hout⟩ :=
          (table_result_iff_valid c out
            ⟨.TableT addr lim rt, init⟩).1 hresult
        have hparts :
            TabletypeValidation.tabletypeValid c (.TableT addr lim rt) = true ∧
              ConstExpressionDecision.constantExpressionResult c
                (.RefT rt) init = true := by
          simpa only [tableValid, Bool.and_eq_true] using hvalid
        obtain ⟨htypeValid, hconstValid⟩ := hparts
        have htypeCall :=
          (TabletypeValidation.tabletype_success_iff_valid
            c (.TableT addr lim rt) start start).2 ⟨htypeValid, rfl⟩
        have htarget : CandidateValMatch.InTableVal c (.RefT rt) :=
          (ConstValidatedTarget.tabletype_target_in_extended_and_table
            c addr lim rt start start htypeCall).2
        subst out
        subst finish
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Table_ok_clauses c ⟨.TableT addr lim rt, init⟩))
          start (.success (.of
            ({c with TABLES := c.TABLES ++ [.TableT addr lim rt]} :
              SpecTec.context))) start
        apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Table_ok:clause:0» c ⟨.TableT addr lim rt, init⟩)
          start (.success (.of
            ({c with TABLES := c.TABLES ++ [.TableT addr lim rt]} :
              SpecTec.context))) start
        unfold SpecTec.«Table_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact htypeCall
        apply SpecTecExecution.Eval.bind_success
        · exact (ConstExpressionDecision.constant_expression_result_iff_const_ok
            c (.RefT rt) init start hready hprov hnested htarget).1 hconstValid
        · exact SpecTecExecution.Eval.pure _
      · intro hcall
        cases hcall with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.Table_ok_clauses c ⟨.TableT addr lim rt, init⟩))
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hclause =>
            unfold SpecTec.«Table_ok:clause:0» at hclause
            cases hclause with
            | bind_success htype htail =>
              cases htail with
              | bind_success hconst hpure =>
                cases hpure with
                | pure =>
                  have htypeResult :=
                    (TabletypeValidation.tabletype_success_iff_valid
                      c (.TableT addr lim rt) _ _).1 htype
                  have htarget : CandidateValMatch.InTableVal c (.RefT rt) :=
                    (ConstValidatedTarget.tabletype_target_in_extended_and_table
                      c addr lim rt _ _ htype).2
                  have hconstResult :=
                    (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters
                      c (.RefT rt) init _ _ hready hprov hnested htarget).2 hconst
                  refine ⟨?_, ?_⟩
                  · apply (table_result_iff_valid c _
                      ⟨.TableT addr lim rt, init⟩).2
                    exact ⟨by simpa [tableValid, htypeResult.1,
                      hconstResult.1], rfl⟩
                  · exact hconstResult.2.trans htypeResult.2
          | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.TableDecision
