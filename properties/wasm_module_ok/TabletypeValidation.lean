import properties.wasm_module_ok.ReftypeTotal
import properties.wasm_module_ok.LimitsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.TabletypeValidation

def tabletypeValid (c : SpecTec.context) : SpecTec.tabletype → Bool
  | .TableT .I32AT lim rt =>
      ReftypeTotal.reftypeValid c rt &&
        LimitsValidation.limitsValid 4294967295 lim
  | .TableT .I64AT lim rt =>
      ReftypeTotal.reftypeValid c rt &&
        LimitsValidation.limitsValid 18446744073709551615 lim

def tabletypeOutcome (c : SpecTec.context) (tt : SpecTec.tabletype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if tabletypeValid c tt then .success (.of ()) else .unmatch

theorem tabletype_i32_clause_total (c : SpecTec.context)
    (lim : SpecTec.limits) (rt : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Tabletype_ok:clause:0» c (.TableT .I32AT lim rt))
      n (tabletypeOutcome c (.TableT .I32AT lim rt)) n := by
  cases hr : ReftypeTotal.reftypeValid c rt with
  | false =>
    unfold SpecTec.«Tabletype_ok:clause:0»
    simp only [tabletypeOutcome, tabletypeValid, hr,
      Bool.false_and]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      simpa [ReftypeTotal.reftypeOutcome, hr] using
        ReftypeTotal.reftype_total c rt n
  | true =>
    cases hl : LimitsValidation.limitsValid 4294967295 lim with
    | false =>
      unfold SpecTec.«Tabletype_ok:clause:0»
      simp only [tabletypeOutcome, tabletypeValid, hr, hl,
        Bool.true_and]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · simpa [ReftypeTotal.reftypeOutcome, hr] using
            ReftypeTotal.reftype_total c rt n
        · apply SpecTecExecution.Eval.bind_unmatch
          exact LimitsValidation.limits_invalid_unmatch
            c 4294967295 lim n hl
    | true =>
      unfold SpecTec.«Tabletype_ok:clause:0»
      simp only [tabletypeOutcome, tabletypeValid, hr, hl,
        Bool.true_and]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · simpa [ReftypeTotal.reftypeOutcome, hr] using
            ReftypeTotal.reftype_total c rt n
        · apply SpecTecExecution.Eval.bind_success
          · exact (LimitsValidation.limits_success_iff_valid
              c 4294967295 lim n n).2 ⟨hl, rfl⟩
          · exact SpecTecExecution.Eval.pure ()

theorem tabletype_i64_clause_total (c : SpecTec.context)
    (lim : SpecTec.limits) (rt : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Tabletype_ok:clause:1» c (.TableT .I64AT lim rt))
      n (tabletypeOutcome c (.TableT .I64AT lim rt)) n := by
  cases hr : ReftypeTotal.reftypeValid c rt with
  | false =>
    unfold SpecTec.«Tabletype_ok:clause:1»
    simp only [tabletypeOutcome, tabletypeValid, hr,
      Bool.false_and]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      simpa [ReftypeTotal.reftypeOutcome, hr] using
        ReftypeTotal.reftype_total c rt n
  | true =>
    cases hl : LimitsValidation.limitsValid 18446744073709551615 lim with
    | false =>
      unfold SpecTec.«Tabletype_ok:clause:1»
      simp only [tabletypeOutcome, tabletypeValid, hr, hl,
        Bool.true_and]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · simpa [ReftypeTotal.reftypeOutcome, hr] using
            ReftypeTotal.reftype_total c rt n
        · apply SpecTecExecution.Eval.bind_unmatch
          exact LimitsValidation.limits_invalid_unmatch
            c 18446744073709551615 lim n hl
    | true =>
      unfold SpecTec.«Tabletype_ok:clause:1»
      simp only [tabletypeOutcome, tabletypeValid, hr, hl,
        Bool.true_and]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · simpa [ReftypeTotal.reftypeOutcome, hr] using
            ReftypeTotal.reftype_total c rt n
        · apply SpecTecExecution.Eval.bind_success
          · exact (LimitsValidation.limits_success_iff_valid
              c 18446744073709551615 lim n n).2 ⟨hl, rfl⟩
          · exact SpecTecExecution.Eval.pure ()

theorem tabletype_total (c : SpecTec.context)
    (tt : SpecTec.tabletype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Tabletype_ok c tt⟩)
      n (tabletypeOutcome c tt) n := by
  cases tt with
  | TableT addr lim rt =>
    cases addr with
    | I32AT =>
      cases hv : tabletypeValid c (.TableT .I32AT lim rt) with
      | true =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tabletype_ok_clauses c (.TableT .I32AT lim rt)))
          n (tabletypeOutcome c (.TableT .I32AT lim rt)) n
        simp only [tabletypeOutcome, hv, ite_true]
        apply SpecTecExecution.tryClauses_cons_success
        simpa [tabletypeOutcome, hv] using
          tabletype_i32_clause_total c lim rt n
      | false =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tabletype_ok_clauses c (.TableT .I32AT lim rt)))
          n (tabletypeOutcome c (.TableT .I32AT lim rt)) n
        simp only [tabletypeOutcome, hv]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · simpa [tabletypeOutcome, hv] using
            tabletype_i32_clause_total c lim rt n
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«Tabletype_ok:clause:1» c (.TableT .I32AT lim rt))
              n .unmatch n
            unfold SpecTec.«Tabletype_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            change ¬ false = true
            decide
          · exact SpecTecExecution.tryClauses_nil n
    | I64AT =>
      cases hv : tabletypeValid c (.TableT .I64AT lim rt) with
      | true =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tabletype_ok_clauses c (.TableT .I64AT lim rt)))
          n (tabletypeOutcome c (.TableT .I64AT lim rt)) n
        simp only [tabletypeOutcome, hv, ite_true]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Tabletype_ok:clause:0» c (.TableT .I64AT lim rt))
            n .unmatch n
          unfold SpecTec.«Tabletype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          change ¬ false = true
          decide
        · apply SpecTecExecution.tryClauses_cons_success
          simpa [tabletypeOutcome, hv] using
            tabletype_i64_clause_total c lim rt n
      | false =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.Tabletype_ok_clauses c (.TableT .I64AT lim rt)))
          n (tabletypeOutcome c (.TableT .I64AT lim rt)) n
        simp only [tabletypeOutcome, hv]
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«Tabletype_ok:clause:0» c (.TableT .I64AT lim rt))
            n .unmatch n
          unfold SpecTec.«Tabletype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          change ¬ false = true
          decide
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · simpa [tabletypeOutcome, hv] using
              tabletype_i64_clause_total c lim rt n
          · exact SpecTecExecution.tryClauses_nil n

theorem tabletype_success_iff_valid (c : SpecTec.context)
    (tt : SpecTec.tabletype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Tabletype_ok c tt⟩)
      n (.success (.of ())) finalSupply ↔
    tabletypeValid c tt = true ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (tabletype_total c tt n)
    cases hv : tabletypeValid c tt with
    | true => exact ⟨rfl, hsupply⟩
    | false => simp [tabletypeOutcome, hv] at hout
  · rintro ⟨hv, rfl⟩
    simpa [tabletypeOutcome, hv] using tabletype_total c tt finalSupply

end properties.wasm_module_ok.TabletypeValidation
