import properties.wasm_module_ok.ConstExpressionDecision
import properties.wasm_module_ok.ConstValidatedTarget

set_option autoImplicit false

namespace properties.wasm_module_ok.GlobalDecision

def globalValid (c : SpecTec.context) (g : SpecTec.global) : Bool :=
  match g.GTYPE with
  | .GlobalT _ t =>
      GlobaltypeValidation.globaltypeValid c g.GTYPE &&
        ConstExpressionDecision.constantExpressionResult c t g.GINIT

def globalResult (c : SpecTec.context) (g : SpecTec.global) :
    Option SpecTec.context :=
  if globalValid c g then
    some {c with GLOBALS := c.GLOBALS ++ [g.GTYPE]}
  else none

theorem global_result_iff_valid
    (c out : SpecTec.context) (g : SpecTec.global) :
    globalResult c g = some out ↔
      globalValid c g = true ∧
        out = {c with GLOBALS := c.GLOBALS ++ [g.GTYPE]} := by
  cases hvalid : globalValid c g <;>
    simp [globalResult, hvalid, eq_comm]

theorem global_result_iff_call
    (c out : SpecTec.context) (g : SpecTec.global)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    globalResult c g = some out ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Global_ok c g⟩)
        start (.success (.of out)) finish := by
  cases g with
  | mk gt init =>
    cases gt with
    | GlobalT mutation t =>
      constructor
      · rintro ⟨hresult, hfinish⟩
        obtain ⟨hvalid, hout⟩ :=
          (global_result_iff_valid c out
            ⟨.GlobalT mutation t, init⟩).1 hresult
        have hparts :
            GlobaltypeValidation.globaltypeValid c (.GlobalT mutation t) = true ∧
              ConstExpressionDecision.constantExpressionResult c t init = true := by
          simpa only [globalValid, Bool.and_eq_true] using hvalid
        obtain ⟨htypeValid, hconstValid⟩ := hparts
        have htarget : CandidateValMatch.InTableVal c t :=
          (ConstValidatedTarget.valid_target_in_extended_and_table c t
            (by simpa [GlobaltypeValidation.globaltypeValid] using htypeValid)).2
        subst out
        subst finish
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Global_ok_clauses c ⟨.GlobalT mutation t, init⟩) ())
          start (.success (.of
            ({c with GLOBALS := c.GLOBALS ++ [.GlobalT mutation t]} :
              SpecTec.context))) start
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Global_ok:clause:0» c ⟨.GlobalT mutation t, init⟩)
          start (.success (.of
            ({c with GLOBALS := c.GLOBALS ++ [.GlobalT mutation t]} :
              SpecTec.context))) start
        unfold SpecTec.«Global_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact (GlobaltypeValidation.globaltype_success_iff_valid
            c (.GlobalT mutation t) start start).2
            ⟨htypeValid, rfl⟩
        apply SpecTecExecution.Eval.bind_success
        · exact (ConstExpressionDecision.constant_expression_result_iff_const_ok
            c t init start hready hprov hnested htarget).1 hconstValid
        · exact SpecTecExecution.Eval.pure _
      · intro hcall
        cases hcall with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.Global_ok_clauses c ⟨.GlobalT mutation t, init⟩) ())
            start (.success (.of out)) finish at hbody
          cases hbody with
          | orElse_success hclause =>
            unfold SpecTec.«Global_ok:clause:0» at hclause
            cases hclause with
            | bind_success htype htail =>
              cases htail with
              | bind_success hconst hpure =>
                cases hpure with
                | pure =>
                  have htypeResult :=
                    (GlobaltypeValidation.globaltype_success_iff_valid
                      c (.GlobalT mutation t) _ _).1 htype
                  have htarget : CandidateValMatch.InTableVal c t :=
                    (ConstValidatedTarget.valid_target_in_extended_and_table
                      c t (by simpa [GlobaltypeValidation.globaltypeValid]
                        using htypeResult.1)).2
                  have hconstResult :=
                    (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters
                      c t init _ _ hready hprov hnested htarget).2 hconst
                  refine ⟨?_, ?_⟩
                  · apply (global_result_iff_valid c _
                      ⟨.GlobalT mutation t, init⟩).2
                    exact ⟨by simpa [globalValid, htypeResult.1,
                      hconstResult.1], rfl⟩
                  · exact hconstResult.2.trans htypeResult.2
          | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.GlobalDecision
