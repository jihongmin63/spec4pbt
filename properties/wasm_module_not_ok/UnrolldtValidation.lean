import properties.wasm_module_not_ok.RectypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

/-- The computable result selected by `$unrolldt` after structural unrolling. -/
def unrollDeftypeResult (dt : SpecTec.deftype) : Option SpecTec.subtype :=
  match dt with
  | .DefT rect n =>
      match unrollRectype rect rect with
      | .RecT sts => sts[n]?

private theorem unrolldt_some (sts : List SpecTec.subtype)
    (n start : Nat) (st : SpecTec.subtype)
    (hget : (unrollSubtypes sts (.RecT sts))[n]? = some st) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.subtype,
        SpecTec.Call.«$unrolldt» (.DefT (.RecT sts) n)⟩)
      start (.success (.of st)) start := by
  have hbound : n < (unrollSubtypes sts (.RecT sts)).length := by
    by_contra h
    have hnone : (unrollSubtypes sts (.RecT sts))[n]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt h)
    rw [hget] at hnone
    cases hnone
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$unrolldt_clauses» (.DefT (.RecT sts) n)))
    start (.success (.of st)) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$unrolldt:clause:0» (.DefT (.RecT sts) n))
    start (.success (.of st)) start
  unfold SpecTec.«$unrolldt:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (unrollrt_total (.RecT sts) start)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simpa [unrollRectype] using hbound)
  · simpa [unrollRectype, hget] using
      (SpecTecExecution.Eval.pure st (n := start))

private theorem unrolldt_none (sts : List SpecTec.subtype)
    (n start : Nat)
    (hget : (unrollSubtypes sts (.RecT sts))[n]? = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.subtype,
        SpecTec.Call.«$unrolldt» (.DefT (.RecT sts) n)⟩)
      start .unmatch start := by
  have hbound : ¬ n < (unrollSubtypes sts (.RecT sts)).length := by
    have hle : (unrollSubtypes sts (.RecT sts)).length ≤ n :=
      List.getElem?_eq_none_iff.mp hget
    omega
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$unrolldt_clauses» (.DefT (.RecT sts) n)))
    start .unmatch start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$unrolldt:clause:0» (.DefT (.RecT sts) n))
      start .unmatch start
    unfold SpecTec.«$unrolldt:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (unrollrt_total (.RecT sts) start)
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simpa [unrollRectype] using hbound)
  · exact SpecTecExecution.tryClauses_nil start

def unrollDeftypeOutcome (dt : SpecTec.deftype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match unrollDeftypeResult dt with
  | some st => .success (.of st)
  | none => .unmatch

theorem unrolldt_total (dt : SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.subtype, SpecTec.Call.«$unrolldt» dt⟩)
      start (unrollDeftypeOutcome dt) start := by
  cases dt with
  | DefT rect n =>
      cases rect with
      | RecT sts =>
          cases hget : (unrollSubtypes sts (.RecT sts))[n]? with
          | none =>
              simpa [unrollDeftypeOutcome, unrollDeftypeResult,
                unrollRectype, hget] using unrolldt_none sts n start hget
          | some st =>
              simpa [unrollDeftypeOutcome, unrollDeftypeResult,
                unrollRectype, hget] using unrolldt_some sts n start st hget

theorem unrolldt_deterministic (dt : SpecTec.deftype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.subtype, SpecTec.Call.«$unrolldt» dt⟩)
      start outcome finalSupply) :
    outcome = unrollDeftypeOutcome dt ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (unrolldt_total dt start)

end properties.wasm_module_not_ok.Rejection
