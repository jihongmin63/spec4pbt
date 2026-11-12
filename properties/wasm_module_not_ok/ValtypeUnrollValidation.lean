import properties.wasm_module_not_ok.ReftypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollValtype (t : SpecTec.valtype) (rect : SpecTec.rectype) : SpecTec.valtype :=
  match t with
  | .RefT rt => .RefT (unrollReftype rt rect)
  | other => other

theorem subst_valtype_unroll_total (t : SpecTec.valtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$subst_valtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» t⟩)
      start (.success (.of (unrollValtype t rect))) start := by
  cases t with
  | NumT nt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_valtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.NumT nt)))
        start (.success (.of (unrollValtype (.NumT nt) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_valtype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.NumT nt))
        start (.success (.of (unrollValtype (.NumT nt) rect))) start
      unfold SpecTec.«$subst_valtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · exact SpecTecExecution.Eval.pure (SpecTec.valtype.NumT nt)
  | VecT vt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_valtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.VecT vt)))
        start (.success (.of (unrollValtype (.VecT vt) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_valtype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.VecT vt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_valtype:clause:1» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.VecT vt))
          start (.success (.of (unrollValtype (.VecT vt) rect))) start
        unfold SpecTec.«$subst_valtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · exact SpecTecExecution.Eval.pure (SpecTec.valtype.VecT vt)
  | RefT rt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_valtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.RefT rt)))
        start (.success (.of (unrollValtype (.RefT rt) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_valtype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.RefT rt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_valtype:clause:1» SpecTec.rectype rect
              SpecTec.Call.«$s_unroll» (.RefT rt)) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_valtype:clause:2» SpecTec.rectype rect
              SpecTec.Call.«$s_unroll» (.RefT rt))
            start (.success (.of (unrollValtype (.RefT rt) rect))) start
          unfold SpecTec.«$subst_valtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.Eval.bind_success
              (subst_reftype_unroll_total rt rect start)
            exact SpecTecExecution.Eval.pure
              (SpecTec.valtype.RefT (unrollReftype rt rect))
  | BotT =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_valtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» .BotT))
        start (.success (.of (unrollValtype .BotT rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_valtype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» .BotT) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_valtype:clause:1» SpecTec.rectype rect
              SpecTec.Call.«$s_unroll» .BotT) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_valtype:clause:2» SpecTec.rectype rect
                SpecTec.Call.«$s_unroll» .BotT) start .unmatch start
            unfold SpecTec.«$subst_valtype:clause:2»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.tryClauses_cons_success
            change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_valtype:clause:3» SpecTec.rectype rect
                SpecTec.Call.«$s_unroll» .BotT)
              start (.success (.of (unrollValtype .BotT rect))) start
            unfold SpecTec.«$subst_valtype:clause:3»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.pure SpecTec.valtype.BotT

theorem subst_valtype_unroll_deterministic (t : SpecTec.valtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$subst_valtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» t⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollValtype t rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_valtype_unroll_total t rect start)

end properties.wasm_module_not_ok.Rejection
