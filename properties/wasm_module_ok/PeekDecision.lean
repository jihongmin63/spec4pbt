import properties.wasm_module_ok.RevDecision
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.PeekDecision

def peekResult (n : Nat) (irt : SpecTec.inferresulttype) :
    SpecTec.valtype :=
  (irt.2.reverse[n]?).getD .BotT

theorem peek_total (n : Nat) (irt : SpecTec.inferresulttype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype, SpecTec.Call.«$peek» n irt⟩)
      start (.success (.of (peekResult n irt))) start := by
  rcases irt with ⟨ell, ts⟩
  by_cases hlt : n < ts.length
  · have hrev : n < ts.reverse.length := by simpa using hlt
    have hget : ts.reverse[n]? = some ts.reverse[n] :=
      List.getElem?_eq_getElem hrev
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$peek_clauses» n (ell, ts)))
      start (.success (.of (peekResult n (ell, ts)))) start
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$peek:clause:0» n (ell, ts))
      start (.success (.of (peekResult n (ell, ts)))) start
    unfold SpecTec.«$peek:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hlt
    · apply SpecTecExecution.Eval.bind_success
        (RevDecision.rev_total SpecTec.valtype ts start)
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hrev
      · apply SpecTecExecution.Eval.bind_success
          (RevDecision.rev_total SpecTec.valtype ts start)
        simpa only [hget, peekResult, Option.getD_some] using
          (SpecTecExecution.Eval.pure ts.reverse[n])
  · have hnone : ts.reverse[n]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt hlt)
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$peek_clauses» n (ell, ts)))
      start (.success (.of (peekResult n (ell, ts)))) start
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$peek:clause:0» n (ell, ts))
        start .unmatch start
      unfold SpecTec.«$peek:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false hlt
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$peek:clause:1» n (ell, ts))
        start (.success (.of (peekResult n (ell, ts)))) start
      unfold SpecTec.«$peek:clause:1»
      simpa [peekResult, hnone] using
        (SpecTecExecution.Eval.pure SpecTec.valtype.BotT)

theorem peek_success_iff_result
    (n : Nat) (irt : SpecTec.inferresulttype)
    (t : SpecTec.valtype) (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype, SpecTec.Call.«$peek» n irt⟩)
      start (.success (.of t)) fin ↔
    t = peekResult n irt ∧ fin = start := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (peek_total n irt start)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact peek_total n irt fin

end properties.wasm_module_ok.PeekDecision
