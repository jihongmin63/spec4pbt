import properties.wasm_module_ok.MatchNullValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchReftypeConditional

def matchReftypeResult (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.reftype → SpecTec.reftype → Bool
  | .«% %» n1 h1, .«% %» n2 h2 =>
      MatchNullValidation.matchNullResult n1 n2 && heapMatch h1 h2

theorem match_reftype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h1 h2 n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (a b : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_reftype» dts a b⟩)
      n (.success (.of (matchReftypeResult heapMatch a b))) n := by
  cases a with
  | «% %» n1 h1 =>
    cases b with
    | «% %» n2 h2 =>
      cases hr : MatchNullValidation.matchNullResult n1 n2 && heapMatch h1 h2 with
      | true =>
        have hg : MatchNullValidation.matchNullResult n1 n2 = true ∧
            heapMatch h1 h2 = true := by
          cases hn : MatchNullValidation.matchNullResult n1 n2 <;>
            cases hh : heapMatch h1 h2 <;> simp_all
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«$match_reftype_clauses» dts
              (.«% %» n1 h1) (.«% %» n2 h2)) ())
          n (.success (.of (matchReftypeResult heapMatch
            (.«% %» n1 h1) (.«% %» n2 h2)))) n
        simp only [matchReftypeResult, hr]
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_reftype:clause:0» dts
            (.«% %» n1 h1) (.«% %» n2 h2))
          n (.success (.of true)) n
        unfold SpecTec.«$match_reftype:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact MatchNullValidation.match_null_total n1 n2 n
        · apply SpecTecExecution.Eval.bind_success
          · exact hheap h1 h2 n
          · exact SpecTecExecution.Eval.bind_success
              (SpecTecExecution.Eval.guard_true hg)
              (SpecTecExecution.Eval.pure true)
      | false =>
        have hg : ¬ (MatchNullValidation.matchNullResult n1 n2 = true ∧
            heapMatch h1 h2 = true) := by
          cases hn : MatchNullValidation.matchNullResult n1 n2 <;>
            cases hh : heapMatch h1 h2 <;> simp_all
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«$match_reftype_clauses» dts
              (.«% %» n1 h1) (.«% %» n2 h2)) ())
          n (.success (.of (matchReftypeResult heapMatch
            (.«% %» n1 h1) (.«% %» n2 h2)))) n
        simp only [matchReftypeResult, hr]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_reftype:clause:0» dts
              (.«% %» n1 h1) (.«% %» n2 h2)) n .unmatch n
          unfold SpecTec.«$match_reftype:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact MatchNullValidation.match_null_total n1 n2 n
          · apply SpecTecExecution.Eval.bind_success
            · exact hheap h1 h2 n
            · exact SpecTecExecution.Eval.bind_unmatch
                (SpecTecExecution.Eval.guard_false hg)
        · apply SpecTecExecution.firstSuccess_cons_success
          exact SpecTecExecution.Eval.pure false

end properties.wasm_module_ok.MatchReftypeConditional
