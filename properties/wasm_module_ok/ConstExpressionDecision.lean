import properties.wasm_module_ok.ConstFoldTrace
import properties.wasm_module_ok.ConstDecisionTrace
import properties.wasm_module_ok.ConstFinalPopShape

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExpressionDecision

/-- Decide a constant expression by folding its instruction effects and
checking the translated final `$pop` against the requested single result. -/
def constantExpressionResult (c : SpecTec.context)
    (t : SpecTec.valtype) (xs : SpecTec.const) : Bool :=
  match ConstFoldDecision.constantFoldResult c [] xs with
  | some (.NoEllipses, stack) =>
      match PopNoEllipsesDecision.popResult c [t] stack with
      | some (.NoEllipses, []) => true
      | _ => false
  | _ => false

theorem constant_expression_result_iff_components
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) :
    constantExpressionResult c t xs = true ↔
      ∃ stack : List SpecTec.valtype,
        ConstFoldDecision.constantFoldResult c [] xs =
          some (.NoEllipses, stack) ∧
        PopNoEllipsesDecision.popResult c [t] stack =
          some (.NoEllipses, []) := by
  constructor
  · intro h
    unfold constantExpressionResult at h
    cases hf : ConstFoldDecision.constantFoldResult c [] xs with
    | none => simp [hf] at h
    | some final =>
        cases final with
        | mk dots stack =>
            cases dots with
            | Ellipses => simp [hf] at h
            | NoEllipses =>
                cases hp : PopNoEllipsesDecision.popResult c [t] stack with
                | none => simp [hf, hp] at h
                | some popped =>
                    cases popped with
                    | mk dots remaining =>
                        cases dots with
                        | Ellipses => simp [hf, hp] at h
                        | NoEllipses =>
                            cases remaining with
                            | nil => exact ⟨stack, rfl, hp⟩
                            | cons head tail => simp [hf, hp] at h
  · rintro ⟨stack, hf, hp⟩
    simp [constantExpressionResult, hf, hp]

theorem constant_expression_result_iff_const_ok
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htarget : CandidateValMatch.InTableVal c t) :
    constantExpressionResult c t xs = true ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        n (.success (.of ())) n := by
  have hadmissible : ConstFoldTrace.FoldAdmissible c [] xs :=
    ConstFoldTrace.fold_admissible_of_provenance
      c xs hready hprov hnested [] (by intro u hu; cases hu)
  have htargetList : ∀ u ∈ [t],
      CandidateValMatch.InTableVal c u := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst u
    exact htarget
  constructor
  · intro hresult
    obtain ⟨stack, hfold, hpop⟩ :=
      (constant_expression_result_iff_components c t xs).1 hresult
    obtain ⟨hsyntax, hinstr⟩ :=
      (ConstFoldTrace.constant_fold_empty_stack_iff_instrs_ok
        c xs (.NoEllipses, stack) n hready hprov hnested).1 hfold
    have hstack : ∀ u ∈ stack,
        CandidateValMatch.InTableVal c u :=
      ConstFoldTrace.constant_fold_result_entries_in_table
        c [] xs (.NoEllipses, stack) hadmissible hfold
    have hpopCall :=
      (PopNoEllipsesDecision.pop_result_iff
        c [t] stack (.NoEllipses, []) n
        hready htargetList hstack).1 hpop
    exact (ConstDecisionTrace.const_ok_decision_trace_iff
      c t xs n n).2
      ⟨hsyntax, (.NoEllipses, stack), [], .NoEllipses, n,
        hinstr, hpopCall⟩
  · intro hcall
    obtain ⟨hsyntax, irt, indices, ellipses, middle,
      hinstr, hpop⟩ :=
      (ConstDecisionTrace.const_ok_decision_trace_iff
        c t xs n n).1 hcall
    obtain ⟨final, hfold, hresult, _⟩ :=
      ConstFoldTrace.constant_instrs_trace_normalize
        c [] xs (irt, indices) n middle hready
        hadmissible hsyntax hinstr
    have hirt : irt = final := congrArg Prod.fst hresult
    obtain ⟨stack, hshape⟩ :=
      ConstFoldDecision.constant_fold_result_concrete_stack
        c [] xs final hfold
    have hfoldStack : ConstFoldDecision.constantFoldResult c [] xs =
        some (.NoEllipses, stack) := by
      simpa only [hshape] using hfold
    have hpopStack : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [t]) (.NoEllipses, stack)⟩)
        middle (.success (.of
          (ellipses, ([] : List SpecTec.valtype)))) n := by
      simpa only [hirt, hshape] using hpop
    have hstack : ∀ u ∈ stack,
        CandidateValMatch.InTableVal c u :=
      ConstFoldTrace.constant_fold_result_entries_in_table
        c [] xs (.NoEllipses, stack) hadmissible hfoldStack
    obtain ⟨hpopResult, _⟩ :=
      (PopNoEllipsesDecision.pop_result_iff_any_counters
        c [t] stack (ellipses, []) middle n
        hready htargetList hstack).2 hpopStack
    obtain ⟨_, _, hellipses⟩ :=
      ConstFinalPopShape.final_const_pop_singleton
        c t stack ellipses middle n hpopStack
    apply (constant_expression_result_iff_components c t xs).2
    exact ⟨stack, hfoldStack, by simpa only [hellipses] using hpopResult⟩

/-- Successful translated constant expressions cannot advance the execution
counter. The executable decision therefore covers calls nested at arbitrary
counter positions in a module validation trace. -/
theorem constant_expression_result_iff_const_ok_any_counters
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htarget : CandidateValMatch.InTableVal c t) :
    constantExpressionResult c t xs = true ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        start (.success (.of ())) finish := by
  constructor
  · rintro ⟨hresult, hsame⟩
    subst finish
    exact (constant_expression_result_iff_const_ok
      c t xs start hready hprov hnested htarget).1 hresult
  · intro hcall
    have hadmissible : ConstFoldTrace.FoldAdmissible c [] xs :=
      ConstFoldTrace.fold_admissible_of_provenance
        c xs hready hprov hnested [] (by intro u hu; cases hu)
    obtain ⟨hsyntax, irt, indices, ellipses, middle,
      hinstr, hpop⟩ :=
      (ConstDecisionTrace.const_ok_decision_trace_iff
        c t xs start finish).1 hcall
    obtain ⟨final, hfold, hresult, hmiddle⟩ :=
      ConstFoldTrace.constant_instrs_trace_normalize
        c [] xs (irt, indices) start middle hready
        hadmissible hsyntax hinstr
    have hirt : irt = final := congrArg Prod.fst hresult
    obtain ⟨stack, hshape⟩ :=
      ConstFoldDecision.constant_fold_result_concrete_stack
        c [] xs final hfold
    have hfoldStack : ConstFoldDecision.constantFoldResult c [] xs =
        some (.NoEllipses, stack) := by
      simpa only [hshape] using hfold
    have hpopStack : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [t]) (.NoEllipses, stack)⟩)
        middle (.success (.of
          (ellipses, ([] : List SpecTec.valtype)))) finish := by
      simpa only [hirt, hshape] using hpop
    have hstack : ∀ u ∈ stack,
        CandidateValMatch.InTableVal c u :=
      ConstFoldTrace.constant_fold_result_entries_in_table
        c [] xs (.NoEllipses, stack) hadmissible hfoldStack
    have htargetList : ∀ u ∈ [t],
        CandidateValMatch.InTableVal c u := by
      intro u hu
      simp only [List.mem_singleton] at hu
      subst u
      exact htarget
    have hfinish : finish = middle :=
      ((PopNoEllipsesDecision.pop_result_iff_any_counters
        c [t] stack (ellipses, []) middle finish
        hready htargetList hstack).2 hpopStack).2
    have hsame : finish = start := hfinish.trans hmiddle
    have hcallSame : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        start (.success (.of ())) start := by
      simpa only [hsame] using hcall
    exact ⟨(constant_expression_result_iff_const_ok
      c t xs start hready hprov hnested htarget).2 hcallSame,
      hsame⟩

end properties.wasm_module_ok.ConstExpressionDecision
