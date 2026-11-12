import properties.wasm_module_ok.MinValidation
import properties.wasm_module_ok.MatchResulttypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.PopGeneralValidation

theorem pop_noellipses_clause3_of_match
    (c : SpecTec.context) (ts₁ ts₂ : List SpecTec.valtype)
    (start finalSupply : Nat)
    (hlen : ts₁.length ≤ ts₂.length)
    (hmatch : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c
        (ts₂.drop (ts₂.length - ts₁.length)) ts₁⟩)
      start (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:3» c (.NoEllipses, ts₁) (.NoEllipses, ts₂))
      start (.success (.of
        (SpecTec.ellipses.NoEllipses,
          ts₂.take (ts₂.length - ts₁.length)))) finalSupply := by
  have hdiff :
      Int.ofNat ts₂.length - Int.ofNat ts₁.length =
        Int.ofNat (ts₂.length - ts₁.length) :=
    (Int.ofNat_sub hlen).symm
  have hbound : ts₂.length - ts₁.length + ts₁.length ≤ ts₂.length := by
    omega
  have htailLength :
      (ts₂.drop (ts₂.length - ts₁.length)).length = ts₁.length := by
    simp [List.length_drop]
    omega
  have htake :
      (ts₂.drop (ts₂.length - ts₁.length)).take ts₁.length =
        ts₂.drop (ts₂.length - ts₁.length) :=
    List.take_of_length_le (by omega)
  unfold SpecTec.«$pop:clause:3»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
        (MinValidation.min_total ts₁.length ts₂.length start)
      simp only [Nat.min_eq_left hlen]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simpa using hlen)
      · simp only [Int.toNat?, hdiff]
        apply SpecTecExecution.Eval.bind_success
        · unfold SpecTecExecution.require
          exact SpecTecExecution.Eval.orElse_success
            (SpecTecExecution.Eval.guard_true hbound)
        · rw [htake]
          apply SpecTecExecution.Eval.bind_success hmatch
          apply SpecTecExecution.Eval.bind_success
          · unfold SpecTecExecution.require
            exact SpecTecExecution.Eval.orElse_success
              (SpecTecExecution.Eval.guard_true (by omega))
          · simpa using (SpecTecExecution.Eval.pure
              (SpecTec.ellipses.NoEllipses,
                ts₂.take (ts₂.length - ts₁.length))
              (n := finalSupply))

theorem pop_noellipses_of_match
    (c : SpecTec.context) (ts₁ ts₂ : List SpecTec.valtype)
    (start finalSupply : Nat)
    (hlen : ts₁.length ≤ ts₂.length)
    (hmatch : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c
        (ts₂.drop (ts₂.length - ts₁.length)) ts₁⟩)
      start (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c (.NoEllipses, ts₁) (.NoEllipses, ts₂)⟩)
      start (.success (.of
        (SpecTec.ellipses.NoEllipses,
          ts₂.take (ts₂.length - ts₁.length)))) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$pop_clauses» c (.NoEllipses, ts₁) (.NoEllipses, ts₂)))
    start (.success (.of
      (SpecTec.ellipses.NoEllipses,
        ts₂.take (ts₂.length - ts₁.length)))) finalSupply
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:0» c (.NoEllipses, ts₁) (.NoEllipses, ts₂))
      start .unmatch start
    unfold SpecTec.«$pop:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:ellipses:Ellipses»])
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$pop:clause:1» c (.NoEllipses, ts₁) (.NoEllipses, ts₂))
        start .unmatch start
      unfold SpecTec.«$pop:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:ellipses:Ellipses»])
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$pop:clause:2» c (.NoEllipses, ts₁) (.NoEllipses, ts₂))
          start .unmatch start
        unfold SpecTec.«$pop:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:ellipses:Ellipses»])
      · apply SpecTecExecution.tryClauses_cons_success
        exact pop_noellipses_clause3_of_match c ts₁ ts₂ start finalSupply hlen hmatch

end properties.wasm_module_ok.PopGeneralValidation
