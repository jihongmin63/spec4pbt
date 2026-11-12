import properties.wasm_module_ok.ValtypeValidation
import properties.wasm_module_ok.ReftypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValtypeTotal

def valtypeOutcome (c : SpecTec.context) (t : SpecTec.valtype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if ValtypeValidation.valtypeValid c t then .success (.of ()) else .unmatch

theorem valtype_total (c : SpecTec.context)
    (t : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c t⟩)
      n (valtypeOutcome c t) n := by
  cases t with
  | NumT nt =>
    simpa [valtypeOutcome, ValtypeValidation.valtypeValid] using
      ValtypeValidation.valtype_num_total c nt n
  | VecT vt =>
    simpa [valtypeOutcome, ValtypeValidation.valtypeValid] using
      ValtypeValidation.valtype_vec_total c vt n
  | RefT rt =>
    cases rt with
    | «% %» nullable ht =>
      cases hv : HeaptypeValidation.heaptypeValid c ht with
      | true =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Valtype_ok_clauses c (.RefT (.«% %» nullable ht))))
          n (valtypeOutcome c (.RefT (.«% %» nullable ht))) n
        simp only [valtypeOutcome, ValtypeValidation.valtypeValid, hv,
          ite_true]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Valtype_ok:clause:0» c (.RefT (.«% %» nullable ht)))
            n .unmatch n
          unfold SpecTec.«Valtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:valtype:NumT»]
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Valtype_ok:clause:1» c (.RefT (.«% %» nullable ht)))
              n .unmatch n
            unfold SpecTec.«Valtype_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp [SpecTec.«exec:match:valtype:VecT»]
          · apply SpecTecExecution.tryClauses_cons_success
            change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Valtype_ok:clause:2» c (.RefT (.«% %» nullable ht)))
              n (.success (.of ())) n
            unfold SpecTec.«Valtype_ok:clause:2»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · apply SpecTecExecution.Eval.bind_success
              · simpa [ReftypeTotal.reftypeOutcome,
                  ReftypeTotal.reftypeValid, hv] using
                  ReftypeTotal.reftype_total c (.«% %» nullable ht) n
              · exact SpecTecExecution.Eval.pure ()
      | false =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Valtype_ok_clauses c (.RefT (.«% %» nullable ht))))
          n (valtypeOutcome c (.RefT (.«% %» nullable ht))) n
        simp only [valtypeOutcome, ValtypeValidation.valtypeValid, hv]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Valtype_ok:clause:0» c (.RefT (.«% %» nullable ht)))
            n .unmatch n
          unfold SpecTec.«Valtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:valtype:NumT»]
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Valtype_ok:clause:1» c (.RefT (.«% %» nullable ht)))
              n .unmatch n
            unfold SpecTec.«Valtype_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp [SpecTec.«exec:match:valtype:VecT»]
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.Body
                (SpecTec.«Valtype_ok:clause:2» c (.RefT (.«% %» nullable ht)))
                n .unmatch n
              unfold SpecTec.«Valtype_ok:clause:2»
              apply SpecTecExecution.Eval.bind_success
              · exact SpecTecExecution.Eval.guard_true rfl
              · apply SpecTecExecution.Eval.bind_unmatch
                simpa [ReftypeTotal.reftypeOutcome,
                  ReftypeTotal.reftypeValid, hv] using
                  ReftypeTotal.reftype_total c (.«% %» nullable ht) n
            · exact SpecTecExecution.tryClauses_nil n
  | BotT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Valtype_ok_clauses c .BotT))
      n (valtypeOutcome c .BotT) n
    simp only [valtypeOutcome, ValtypeValidation.valtypeValid]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Valtype_ok:clause:0» c .BotT) n .unmatch n
      unfold SpecTec.«Valtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Valtype_ok:clause:1» c .BotT) n .unmatch n
        unfold SpecTec.«Valtype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:valtype:VecT»]
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Valtype_ok:clause:2» c .BotT) n .unmatch n
          unfold SpecTec.«Valtype_ok:clause:2»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:valtype:RefT»]
        · exact SpecTecExecution.tryClauses_nil n

end properties.wasm_module_ok.ValtypeTotal
