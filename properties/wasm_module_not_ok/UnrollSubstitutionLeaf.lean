import properties.wasm_module_not_ok.RectypeIterValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollTypevar (tv : SpecTec.typevar) (rect : SpecTec.rectype) :
    SpecTec.heaptype :=
  match tv with
  | .RecX n => .DefHT (.DefT rect n)
  | .StatX n => .VarHT (.StatX n)

theorem s_unroll_total (tv : SpecTec.typevar)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$s_unroll» tv rect⟩)
      start (.success (.of (unrollTypevar tv rect))) start := by
  cases tv with
  | RecX n =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$s_unroll_clauses» (.RecX n) rect) ())
        start (.success (.of (unrollTypevar (.RecX n) rect))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$s_unroll:clause:0» (.RecX n) rect)
        start (.success (.of (unrollTypevar (.RecX n) rect))) start
      unfold SpecTec.«$s_unroll:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:typevar:RecX»])
      · exact SpecTecExecution.Eval.pure
          (SpecTec.heaptype.DefHT (.DefT rect n))
  | StatX n =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$s_unroll_clauses» (.StatX n) rect) ())
        start (.success (.of (unrollTypevar (.StatX n) rect))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$s_unroll:clause:0» (.StatX n) rect)
          start .unmatch start
        unfold SpecTec.«$s_unroll:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:typevar:RecX»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$s_unroll:clause:1» (.StatX n) rect)
          start (.success (.of (unrollTypevar (.StatX n) rect))) start
        exact SpecTecExecution.Eval.pure
          (SpecTec.heaptype.VarHT (.StatX n))

theorem s_unroll_deterministic (tv : SpecTec.typevar)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$s_unroll» tv rect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollTypevar tv rect)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (s_unroll_total tv rect start)

end properties.wasm_module_not_ok.Rejection
