import properties.wasm_module_not_ok.RollingValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollTypevar (tv : SpecTec.typevar) (x y : Nat) : SpecTec.heaptype :=
  match tv with
  | .StatX n =>
      if x ≤ n ∧ n < y then .VarHT (.RecX (n - x)) else .VarHT tv
  | .RecX _ => .VarHT tv

theorem s_roll_rec_total (n x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$s_roll» (.RecX n) (x, y)⟩)
      start (.success (.of (rollTypevar (.RecX n) x y))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$s_roll_clauses» (.RecX n) (x, y)))
    start (.success (.of (rollTypevar (.RecX n) x y))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$s_roll:clause:0» (.RecX n) (x, y)) start .unmatch start
    unfold SpecTec.«$s_roll:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp [SpecTec.«exec:match:typevar:StatX»]
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$s_roll:clause:1» (.RecX n) (x, y))
      start (.success (.of (rollTypevar (.RecX n) x y))) start
    simpa [SpecTec.«$s_roll:clause:1», rollTypevar] using
      (SpecTecExecution.Eval.pure (SpecTec.heaptype.VarHT (.RecX n)) (n := start))

theorem s_roll_stat_outside_total (n x y start : Nat)
    (hout : ¬ (x ≤ n ∧ n < y)) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$s_roll» (.StatX n) (x, y)⟩)
      start (.success (.of (rollTypevar (.StatX n) x y))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$s_roll_clauses» (.StatX n) (x, y)))
    start (.success (.of (rollTypevar (.StatX n) x y))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$s_roll:clause:0» (.StatX n) (x, y)) start .unmatch start
    unfold SpecTec.«$s_roll:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:typevar:StatX»])
    · apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false hout
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$s_roll:clause:1» (.StatX n) (x, y))
      start (.success (.of (rollTypevar (.StatX n) x y))) start
    simpa [SpecTec.«$s_roll:clause:1», rollTypevar, hout] using
      (SpecTecExecution.Eval.pure (SpecTec.heaptype.VarHT (.StatX n)) (n := start))

private theorem roll_sub_cast (n x : Nat) (hx : x ≤ n) :
    Int.ofNat n - Int.ofNat x = Int.ofNat (n - x) := by
  change ((n : Nat) : Int) - ((x : Nat) : Int) = ((n - x : Nat) : Int)
  rw [← Int.ofNat_sub hx]

private theorem roll_sub_nonneg (n x : Nat) (hx : x ≤ n) :
    (0 : Int) ≤ Int.ofNat n - Int.ofNat x := by
  rw [roll_sub_cast n x hx]
  exact Int.natCast_nonneg _

private theorem roll_sub_toNat (n x : Nat) (hx : x ≤ n) :
    (Int.ofNat n - Int.ofNat x).toNat? = some (n - x) := by
  rw [roll_sub_cast n x hx]
  exact Int.mem_toNat?.2 rfl

theorem s_roll_stat_inside_total (n x y start : Nat)
    (hin : x ≤ n ∧ n < y) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$s_roll» (.StatX n) (x, y)⟩)
      start (.success (.of (rollTypevar (.StatX n) x y))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$s_roll_clauses» (.StatX n) (x, y)))
    start (.success (.of (rollTypevar (.StatX n) x y))) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$s_roll:clause:0» (.StatX n) (x, y))
    start (.success (.of (rollTypevar (.StatX n) x y))) start
  unfold SpecTec.«$s_roll:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (by simp [SpecTec.«exec:match:typevar:StatX»])
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hin
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simpa using roll_sub_nonneg n x hin.1)
      · rw [roll_sub_toNat n x hin.1]
        simpa [rollTypevar, hin] using
          (SpecTecExecution.Eval.pure
            (SpecTec.heaptype.VarHT (.RecX (n - x))) (n := start))

theorem s_roll_total (tv : SpecTec.typevar) (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype, SpecTec.Call.«$s_roll» tv (x, y)⟩)
      start (.success (.of (rollTypevar tv x y))) start := by
  cases tv with
  | RecX n => exact s_roll_rec_total n x y start
  | StatX n =>
      by_cases h : x ≤ n ∧ n < y
      · exact s_roll_stat_inside_total n x y start h
      · exact s_roll_stat_outside_total n x y start h

theorem s_roll_deterministic (tv : SpecTec.typevar) (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype, SpecTec.Call.«$s_roll» tv (x, y)⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollTypevar tv x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (s_roll_total tv x y start)

end properties.wasm_module_not_ok.Rejection
