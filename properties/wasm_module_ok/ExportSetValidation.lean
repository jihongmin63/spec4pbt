import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ExportSetValidation

def inSetResult (name : SpecTec.name) : SpecTec.nameset → Bool
  | .«`{ % `}» names =>
      letI : BEq SpecTec.name := instBEqOfDecidableEq
      decide (name ∈ names)

theorem in_set_total (name : SpecTec.name)
    (names : SpecTec.nameset) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$in_set» SpecTec.name name names⟩)
      n (.success (.of (inSetResult name names))) n := by
  cases names with
  | «`{ % `}» xs =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$in_set_clauses» SpecTec.name name (.«`{ % `}» xs)))
      n (.success (.of (inSetResult name (.«`{ % `}» xs)))) n
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$in_set:clause:0» SpecTec.name name (.«`{ % `}» xs))
      n (.success (.of (inSetResult name (.«`{ % `}» xs)))) n
    simpa [SpecTec.«$in_set:clause:0», inSetResult] using
      (SpecTecExecution.Eval.pure (inSetResult name (.«`{ % `}» xs)) :
        SpecTecExecution.Eval SpecTec.Body
          (.pure (inSetResult name (.«`{ % `}» xs))) n
          (.success (.of (inSetResult name (.«`{ % `}» xs)))) n)

theorem in_set_success_iff (name : SpecTec.name)
    (names : SpecTec.nameset) (result : Bool)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$in_set» SpecTec.name name names⟩)
      n (.success (.of result)) finalSupply ↔
    result = inSetResult name names ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (in_set_total name names n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact in_set_total name names finalSupply

end properties.wasm_module_ok.ExportSetValidation
