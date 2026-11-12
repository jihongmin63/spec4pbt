import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.LimitsValidation

def limitsValid (range : SpecTec.range) (lim : SpecTec.limits) : Bool :=
  match lim.MAX with
  | none => decide (lim.MIN ≤ range)
  | some max => decide (lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max)

theorem limits_none_success (c : SpecTec.context)
    (range : SpecTec.range) (lim : SpecTec.limits) (n : Nat)
    (hmax : lim.MAX = none) (hmin : lim.MIN ≤ range) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok c range lim⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Limits_ok_clauses c range lim))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Limits_ok:clause:0» c range lim)
    n (.success (.of ())) n
  unfold SpecTec.«Limits_ok:clause:0»
  rw [hmax]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hmin
    · exact SpecTecExecution.Eval.pure ()

theorem limits_some_success (c : SpecTec.context)
    (range : SpecTec.range) (lim : SpecTec.limits)
    (max : SpecTec.u64) (n : Nat)
    (hmax : lim.MAX = some max)
    (hvalid : lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok c range lim⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Limits_ok_clauses c range lim))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Limits_ok:clause:0» c range lim) n .unmatch n
    unfold SpecTec.«Limits_ok:clause:0»
    rw [hmax]
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Limits_ok:clause:1» c range lim)
      n (.success (.of ())) n
    unfold SpecTec.«Limits_ok:clause:1»
    rw [hmax]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          ⟨⟨hvalid.1, hvalid.2.1⟩, hvalid.2.2⟩
      · exact SpecTecExecution.Eval.pure ()

theorem limits_success_iff_valid (c : SpecTec.context)
    (range : SpecTec.range) (lim : SpecTec.limits)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok c range lim⟩)
      n (.success (.of ())) finalSupply ↔
    limitsValid range lim = true ∧ finalSupply = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Limits_ok_clauses c range lim))
        n (.success (.of ())) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Limits_ok:clause:0» c range lim)
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Limits_ok:clause:1» c range lim]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Limits_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hnone htail =>
          cases hnone with
          | guard_true hnone =>
            cases htail with
            | bind_success hmin hpure =>
              cases hmin with
              | guard_true hmin =>
                cases hpure with
                | pure =>
                  have hmax : lim.MAX = none := by
                    cases hm : lim.MAX <;> simp [hm] at hnone ⊢
                  exact ⟨by simp [limitsValid, hmax, hmin], rfl⟩
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Limits_ok:clause:1» c range lim)
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Limits_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hsome htail =>
            cases hsome with
            | guard_true hsome =>
              cases hm : lim.MAX with
              | none => simp [hm] at hsome
              | some max =>
                rw [hm] at htail
                cases htail with
                | bind_success hvalid hpure =>
                  cases hvalid with
                  | guard_true hvalid =>
                    cases hpure with
                    | pure =>
                      have hv : lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max :=
                        ⟨hvalid.1.1, hvalid.1.2, hvalid.2⟩
                      exact ⟨by simp [limitsValid, hm, hv], rfl⟩
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨hvalid, rfl⟩
    cases hm : lim.MAX with
    | none =>
      have hmin : lim.MIN ≤ range := by
        simpa [limitsValid, hm] using hvalid
      exact limits_none_success c range lim finalSupply hm hmin
    | some max =>
      have hbounds : lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max := by
        have hd : decide (lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max) = true := by
          simpa [limitsValid, hm] using hvalid
        exact of_decide_eq_true hd
      exact limits_some_success c range lim max finalSupply hm hbounds

theorem limits_invalid_unmatch (c : SpecTec.context)
    (range : SpecTec.range) (lim : SpecTec.limits) (n : Nat)
    (hvalid : limitsValid range lim = false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok c range lim⟩)
      n .unmatch n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Limits_ok_clauses c range lim))
    n .unmatch n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Limits_ok:clause:0» c range lim) n .unmatch n
    unfold SpecTec.«Limits_ok:clause:0»
    cases hm : lim.MAX with
    | none =>
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        have hmin : ¬ lim.MIN ≤ range := by
          simpa [limitsValid, hm] using hvalid
        exact hmin
    | some max =>
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Limits_ok:clause:1» c range lim) n .unmatch n
      unfold SpecTec.«Limits_ok:clause:1»
      cases hm : lim.MAX with
      | none =>
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp
      | some max =>
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          have hbounds : ¬ (lim.MIN ≤ range ∧ max ≤ range ∧ lim.MIN ≤ max) := by
            simpa [limitsValid, hm] using hvalid
          intro h
          exact hbounds ⟨h.1.1, h.1.2, h.2⟩
    · exact SpecTecExecution.tryClauses_nil n

def limitsOutcome (range : SpecTec.range) (lim : SpecTec.limits) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if limitsValid range lim then .success (.of ()) else .unmatch

theorem limits_total (c : SpecTec.context)
    (range : SpecTec.range) (lim : SpecTec.limits) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Limits_ok c range lim⟩)
      n (limitsOutcome range lim) n := by
  cases hv : limitsValid range lim with
  | false =>
    simpa [limitsOutcome, hv] using limits_invalid_unmatch c range lim n hv
  | true =>
    simpa [limitsOutcome, hv] using
      (limits_success_iff_valid c range lim n n).2 ⟨hv, rfl⟩

end properties.wasm_module_ok.LimitsValidation
