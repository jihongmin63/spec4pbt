import properties.wasm_module_not_ok.TypesValidation

set_option autoImplicit false
namespace properties.wasm_module_not_ok.Rejection

private theorem predCast (n : Nat) :
    Int.ofNat (n + 1) - Int.ofNat 1 = Int.ofNat n := by
  change ((n + 1 : Nat) : Int) - ((1 : Nat) : Int) = (n : Int)
  rw [← Int.ofNat_sub (show 1 ≤ n + 1 by omega)]
  simp

theorem range_zero_success (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» 0⟩)
      start (.success (.of ([] : List Nat))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$range_clauses» 0) ())
    start (.success (.of ([] : List Nat))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$range:clause:0» 0)
    start (.success (.of ([] : List Nat))) start
  unfold SpecTec.«$range:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure []

theorem range_succ_success (n start : Nat)
    (ih : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» n⟩)
      start (.success (.of (List.range n))) start) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» (n + 1)⟩)
      start (.success (.of (List.range (n + 1)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$range_clauses» (n + 1)) ())
    start (.success (.of (List.range (n + 1)))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$range:clause:0» (n + 1)) start .unmatch start
    unfold SpecTec.«$range:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    omega
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$range:clause:1» (n + 1))
      start (.success (.of (List.range (n + 1)))) start
    unfold SpecTec.«$range:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      simp
    · apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        simp
      · simp only [predCast]
        apply SpecTecExecution.Eval.bind_success ih
        simpa [List.range_succ] using
          (SpecTecExecution.Eval.pure (List.range n ++ [n]) (n := start))


theorem range_total (n start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» n⟩)
      start (.success (.of (List.range n))) start := by
  induction n with
  | zero => exact range_zero_success start
  | succ n ih => simpa [Nat.succ_eq_add_one] using range_succ_success n start ih

theorem range_deterministic (n start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List Nat, SpecTec.SpecTecCall.«$range» n⟩)
      start outcome finalSupply) :
    outcome = .success (.of (List.range n)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (range_total n start)

end properties.wasm_module_not_ok.Rejection
