import properties.wasm_module_ok.MinValidation
import properties.wasm_module_ok.MatchResulttypeValidation
import properties.wasm_module_ok.BlockTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.PopBaseValidation

theorem pop_empty_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, ([] : List SpecTec.valtype))
          (.NoEllipses, ([] : List SpecTec.valtype))⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$pop_clauses» c
        (.NoEllipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype))))
    n (.success (.of
      (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:0» c
        (.NoEllipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype))) n .unmatch n
    unfold SpecTec.«$pop:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp [SpecTec.«exec:match:ellipses:Ellipses»]
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$pop:clause:1» c
          (.NoEllipses, ([] : List SpecTec.valtype))
          (.NoEllipses, ([] : List SpecTec.valtype))) n .unmatch n
      unfold SpecTec.«$pop:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:Ellipses»]
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$pop:clause:2» c
            (.NoEllipses, ([] : List SpecTec.valtype))
            (.NoEllipses, ([] : List SpecTec.valtype))) n .unmatch n
        unfold SpecTec.«$pop:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:Ellipses»]
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$pop:clause:3» c
            (.NoEllipses, ([] : List SpecTec.valtype))
            (.NoEllipses, ([] : List SpecTec.valtype)))
          n (.success (.of
            (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n
        unfold SpecTec.«$pop:clause:3»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · apply SpecTecExecution.Eval.bind_success
              (MinValidation.min_total 0 0 n)
            apply SpecTecExecution.Eval.bind_success
            · apply SpecTecExecution.Eval.guard_true
              rfl
            · apply SpecTecExecution.Eval.bind_success
              · unfold SpecTecExecution.require
                exact SpecTecExecution.Eval.orElse_success
                  (SpecTecExecution.Eval.guard_true (by decide))
              · apply SpecTecExecution.Eval.bind_success
                  (MatchResulttypeValidation.match_resulttype_nil_total c n)
                apply SpecTecExecution.Eval.bind_success
                · unfold SpecTecExecution.require
                  exact SpecTecExecution.Eval.orElse_success
                    (SpecTecExecution.Eval.guard_true (by decide))
                · exact SpecTecExecution.Eval.pure
                    (SpecTec.ellipses.NoEllipses,
                      ([] : List SpecTec.valtype))

theorem block_empty_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Block_ok c
        (.InstrT [] [] []) ([] : SpecTec.const)⟩)
      n (.success (.of ())) n := by
  apply (BlockTrace.block_success_iff c [] [] [] [] n n).2
  exact ⟨(.NoEllipses, []), [], .NoEllipses, n,
    InstrsValidation.instrs_nil_total c (.NoEllipses, []) n,
    pop_empty_total c n⟩

end properties.wasm_module_ok.PopBaseValidation
