import properties.wasm_module_ok.ConstExternCandidate
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ExternopTypeDecision

def typeExternopResult : SpecTec.externop_ →
    SpecTec.heaptype × SpecTec.heaptype
  | .Internalize => (.ExternHT, .AnyHT)
  | .Externalize => (.AnyHT, .ExternHT)

theorem type_externop_total (op : SpecTec.externop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
        SpecTec.Call.«$type_externop» op⟩)
      n (.success (.of (typeExternopResult op))) n := by
  cases op with
  | Internalize =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$type_externop_clauses» .Internalize))
      n (.success (.of (SpecTec.heaptype.ExternHT,
        SpecTec.heaptype.AnyHT))) n
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_externop:clause:0» .Internalize)
      n (.success (.of (SpecTec.heaptype.ExternHT,
        SpecTec.heaptype.AnyHT))) n
    unfold SpecTec.«$type_externop:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure _
  | Externalize =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$type_externop_clauses» .Externalize))
      n (.success (.of (SpecTec.heaptype.AnyHT,
        SpecTec.heaptype.ExternHT))) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_externop:clause:0» .Externalize)
        n .unmatch n
      unfold SpecTec.«$type_externop:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:externop_:Internalize»])
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_externop:clause:1» .Externalize)
        n (.success (.of (SpecTec.heaptype.AnyHT,
          SpecTec.heaptype.ExternHT))) n
      unfold SpecTec.«$type_externop:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure _

theorem type_externop_success_iff_result
    (op : SpecTec.externop_)
    (pair : SpecTec.heaptype × SpecTec.heaptype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
        SpecTec.Call.«$type_externop» op⟩)
      n (.success (.of pair)) finalSupply ↔
    pair = typeExternopResult op ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (type_externop_total op n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact type_externop_total op finalSupply

end properties.wasm_module_ok.ExternopTypeDecision
