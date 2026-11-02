import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MakeValidation

def makeResult {X : Type} (value : X) : Nat → List X
  | 0 => []
  | n + 1 => makeResult value n ++ [value]

theorem make_total (X : Type) (value : X)
    (count start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List X,
        SpecTec.Call.«$make_» X value count⟩)
      start (.success (.of (makeResult value count))) start := by
  induction count generalizing start with
  | zero =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$make__clauses» X value 0))
      start (.success (.of (makeResult value 0))) start
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$make_:clause:0» X value 0)
      start (.success (.of (makeResult value 0))) start
    unfold SpecTec.«$make_:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · exact SpecTecExecution.Eval.pure []
  | succ count ih =>
    have hsub :
        (Int.ofNat (count + 1) - Int.ofNat 1) = Int.ofNat count := by
      simp
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$make__clauses» X value (count + 1)))
      start (.success (.of (makeResult value (count + 1)))) start
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$make_:clause:0» X value (count + 1))
        start .unmatch start
      unfold SpecTec.«$make_:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      omega
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$make_:clause:1» X value (count + 1))
        start (.success (.of (makeResult value (count + 1)))) start
      unfold SpecTec.«$make_:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        simp
      · apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          simp [hsub]
        · simp [hsub]
          apply SpecTecExecution.Eval.bind_success (ih start)
          exact SpecTecExecution.Eval.pure (makeResult value count ++ [value])

theorem make_success_iff (X : Type) (value : X)
    (count : Nat) (result : List X)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List X,
        SpecTec.Call.«$make_» X value count⟩)
      start (.success (.of result)) finalSupply ↔
    result = makeResult value count ∧ finalSupply = start := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (make_total X value count start)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact make_total X value count finalSupply

end properties.wasm_module_ok.MakeValidation
