import properties.wasm_module_ok.PopMatchSaturation
import properties.wasm_module_ok.PopBaseValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSingletonFinalPop

theorem singleton_match_resulttype_of_candidate
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hu : CandidateValMatch.InTableVal c u)
    (ht : CandidateValMatch.InTableVal c t)
    (hmatch : CandidateValMatch.candidateValMatch c u t = true) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c [u] [t]⟩)
      n (.success (.of ())) n := by
  have hvalue : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» c.TYPES u t⟩)
      n (.success (.of true)) n := by
    simpa only [hmatch] using
      (CandidateValMatch.candidate_val_match_total c u t n hready hu ht)
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c [u] [t] n n).2
  refine ⟨rfl, ?_⟩
  exact (MatchResulttypeValidation.match_iter_cons_success_iff
    c u t [] [] n n).2
      ⟨n, hvalue, MatchResulttypeValidation.match_iter_nil_total c n⟩

theorem singleton_final_pop_of_match_resulttype
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c [u] [t]⟩)
      n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (SpecTec.ellipses.NoEllipses, [t])
          (SpecTec.ellipses.NoEllipses, [u])⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses,
          ([] : List SpecTec.valtype)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$pop_clauses» c
        (.NoEllipses, [t]) (.NoEllipses, [u])) ())
    n (.success (.of
      (SpecTec.ellipses.NoEllipses,
        ([] : List SpecTec.valtype)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:0» c
        (.NoEllipses, [t]) (.NoEllipses, [u])) n .unmatch n
    unfold SpecTec.«$pop:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp [SpecTec.«exec:match:ellipses:Ellipses»]
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$pop:clause:1» c
          (.NoEllipses, [t]) (.NoEllipses, [u])) n .unmatch n
      unfold SpecTec.«$pop:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:Ellipses»]
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$pop:clause:2» c
            (.NoEllipses, [t]) (.NoEllipses, [u])) n .unmatch n
        unfold SpecTec.«$pop:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:Ellipses»]
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$pop:clause:3» c
            (.NoEllipses, [t]) (.NoEllipses, [u]))
          n (.success (.of
            (SpecTec.ellipses.NoEllipses,
              ([] : List SpecTec.valtype)))) n
        unfold SpecTec.«$pop:clause:3»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · apply SpecTecExecution.Eval.bind_success
              (MinValidation.min_total 1 1 n)
            apply SpecTecExecution.Eval.bind_success
            · apply SpecTecExecution.Eval.guard_true
              rfl
            · apply SpecTecExecution.Eval.bind_success
              · unfold SpecTecExecution.require
                exact SpecTecExecution.Eval.orElse_success
                  (SpecTecExecution.Eval.guard_true (by simp))
              · apply SpecTecExecution.Eval.bind_success hmatch
                apply SpecTecExecution.Eval.bind_success
                · unfold SpecTecExecution.require
                  exact SpecTecExecution.Eval.orElse_success
                    (SpecTecExecution.Eval.guard_true (by simp))
                · exact SpecTecExecution.Eval.pure
                    (SpecTec.ellipses.NoEllipses,
                      ([] : List SpecTec.valtype))

theorem singleton_final_pop_of_candidate_match
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hu : CandidateValMatch.InTableVal c u)
    (ht : CandidateValMatch.InTableVal c t)
    (hmatch : CandidateValMatch.candidateValMatch c u t = true) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (SpecTec.ellipses.NoEllipses, [t])
          (SpecTec.ellipses.NoEllipses, [u])⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses,
          ([] : List SpecTec.valtype)))) n := by
  exact singleton_final_pop_of_match_resulttype c u t n
    (singleton_match_resulttype_of_candidate c u t n
      hready hu ht hmatch)

end properties.wasm_module_ok.ConstSingletonFinalPop
