import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.PushValidation

def pushResult (a b : SpecTec.inferresulttype) :
    Option SpecTec.inferresulttype :=
  match a, b with
  | (.NoEllipses, ats), (.NoEllipses, bts) =>
      some (.NoEllipses, bts ++ ats)
  | (.NoEllipses, ats), (.Ellipses, bts) =>
      some (.Ellipses, bts ++ ats)
  | (.Ellipses, ats), (_, []) => some (.Ellipses, ats)
  | (.Ellipses, _), (_, _ :: _) => none

def pushOutcome (a b : SpecTec.inferresulttype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match pushResult a b with
  | some result => .success (.of result)
  | none => .unmatch

theorem push_total (c : SpecTec.context)
    (a b : SpecTec.inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c a b⟩)
      n (pushOutcome a b) n := by
  rcases a with ⟨af, ats⟩
  rcases b with ⟨bf, bts⟩
  cases af with
  | NoEllipses =>
    cases bf with
    | NoEllipses =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$push_clauses» c
            (.NoEllipses, ats) (.NoEllipses, bts)) ())
        n (pushOutcome (.NoEllipses, ats) (.NoEllipses, bts)) n
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$push:clause:0» c
          (.NoEllipses, ats) (.NoEllipses, bts))
        n (.success (.of
          (SpecTec.ellipses.NoEllipses, bts ++ ats))) n
      unfold SpecTec.«$push:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · exact SpecTecExecution.Eval.pure
            (SpecTec.ellipses.NoEllipses, bts ++ ats)
    | Ellipses =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$push_clauses» c
            (.NoEllipses, ats) (.Ellipses, bts)) ())
        n (pushOutcome (.NoEllipses, ats) (.Ellipses, bts)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$push:clause:0» c
            (.NoEllipses, ats) (.Ellipses, bts)) n .unmatch n
        unfold SpecTec.«$push:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:ellipses:NoEllipses»]
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$push:clause:1» c
            (.NoEllipses, ats) (.Ellipses, bts))
          n (.success (.of
            (SpecTec.ellipses.Ellipses, bts ++ ats))) n
        unfold SpecTec.«$push:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · exact SpecTecExecution.Eval.pure
              (SpecTec.ellipses.Ellipses, bts ++ ats)
  | Ellipses =>
    cases bts with
    | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$push_clauses» c (.Ellipses, ats) (bf, [])) ())
        n (pushOutcome (.Ellipses, ats) (bf, [])) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$push:clause:0» c (.Ellipses, ats) (bf, []))
          n .unmatch n
        unfold SpecTec.«$push:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:NoEllipses»]
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$push:clause:1» c (.Ellipses, ats) (bf, []))
            n .unmatch n
          unfold SpecTec.«$push:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:ellipses:NoEllipses»]
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$push:clause:2» c (.Ellipses, ats) (bf, []))
            n (.success (.of (SpecTec.ellipses.Ellipses, ats))) n
          unfold SpecTec.«$push:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · apply SpecTecExecution.Eval.bind_success
            · apply SpecTecExecution.Eval.guard_true
              rfl
            · exact SpecTecExecution.Eval.pure
                (SpecTec.ellipses.Ellipses, ats)
    | cons t ts =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$push_clauses» c
            (.Ellipses, ats) (bf, t :: ts)) ())
        n (pushOutcome (.Ellipses, ats) (bf, t :: ts)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$push:clause:0» c
            (.Ellipses, ats) (bf, t :: ts)) n .unmatch n
        unfold SpecTec.«$push:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:ellipses:NoEllipses»]
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$push:clause:1» c
              (.Ellipses, ats) (bf, t :: ts)) n .unmatch n
          unfold SpecTec.«$push:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:ellipses:NoEllipses»]
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$push:clause:2» c
                (.Ellipses, ats) (bf, t :: ts)) n .unmatch n
            unfold SpecTec.«$push:clause:2»
            apply SpecTecExecution.Eval.bind_success
            · apply SpecTecExecution.Eval.guard_true
              rfl
            · apply SpecTecExecution.Eval.bind_unmatch
              apply SpecTecExecution.Eval.guard_false
              simp
          · exact SpecTecExecution.firstSuccess_nil () n

theorem push_deterministic (c : SpecTec.context)
    (a b : SpecTec.inferresulttype) (n finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c a b⟩)
      n outcome finalSupply) :
    outcome = pushOutcome a b ∧ finalSupply = n := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hp
    cases hp
  exact SpecTecExecution.eval_deterministic hdet h
    (push_total c a b n)

theorem push_success_iff_result (c : SpecTec.context)
    (a b result : SpecTec.inferresulttype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c a b⟩)
      n (.success (.of result)) finalSupply ↔
    pushResult a b = some result ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      push_deterministic c a b n finalSupply
        (.success (.of result)) h
    cases hresult : pushResult a b with
    | none => simp [pushOutcome, hresult] at hout
    | some computed =>
      simp [pushOutcome, hresult] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hresult, rfl⟩
    simpa [pushOutcome, hresult] using
      push_total c a b finalSupply

end properties.wasm_module_ok.PushValidation
