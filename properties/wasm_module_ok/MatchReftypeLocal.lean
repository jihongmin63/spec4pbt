import properties.wasm_module_ok.MatchReftypeConditional

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchReftypeLocal

open MatchReftypeConditional

theorem match_reftype_pair_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (n1 n2 : SpecTec.null) (h1 h2 : SpecTec.heaptype) (n : Nat)
    (hheap : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
      n (.success (.of (heapMatch h1 h2))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_reftype» dts
        (.«% %» n1 h1) (.«% %» n2 h2)⟩)
      n (.success (.of
        (MatchReftypeConditional.matchReftypeResult heapMatch
          (.«% %» n1 h1) (.«% %» n2 h2)))) n := by
  cases hr : MatchNullValidation.matchNullResult n1 n2 && heapMatch h1 h2 with
  | true =>
    have hg : MatchNullValidation.matchNullResult n1 n2 = true ∧
        heapMatch h1 h2 = true := by
      cases hn : MatchNullValidation.matchNullResult n1 n2 <;>
        cases hh : heapMatch h1 h2 <;> simp_all
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_reftype_clauses» dts
          (.«% %» n1 h1) (.«% %» n2 h2)))
      n (.success (.of (matchReftypeResult heapMatch
        (.«% %» n1 h1) (.«% %» n2 h2)))) n
    simp only [matchReftypeResult, hr]
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_reftype:clause:0» dts
        (.«% %» n1 h1) (.«% %» n2 h2))
      n (.success (.of true)) n
    unfold SpecTec.«$match_reftype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchNullValidation.match_null_total n1 n2 n
    · apply SpecTecExecution.Eval.bind_success
      · exact hheap
      · exact SpecTecExecution.Eval.bind_success
          (SpecTecExecution.Eval.guard_true hg)
          (SpecTecExecution.Eval.pure true)
  | false =>
    have hg : ¬ (MatchNullValidation.matchNullResult n1 n2 = true ∧
        heapMatch h1 h2 = true) := by
      cases hn : MatchNullValidation.matchNullResult n1 n2 <;>
        cases hh : heapMatch h1 h2 <;> simp_all
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_reftype_clauses» dts
          (.«% %» n1 h1) (.«% %» n2 h2)))
      n (.success (.of (matchReftypeResult heapMatch
        (.«% %» n1 h1) (.«% %» n2 h2)))) n
    simp only [matchReftypeResult, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_reftype:clause:0» dts
          (.«% %» n1 h1) (.«% %» n2 h2)) n .unmatch n
      unfold SpecTec.«$match_reftype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchNullValidation.match_null_total n1 n2 n
      · apply SpecTecExecution.Eval.bind_success
        · exact hheap
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false hg)
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false
end properties.wasm_module_ok.MatchReftypeLocal
