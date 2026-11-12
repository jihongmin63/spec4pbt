import properties.wasm_module_not_ok.CompoundUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollStrtype (strt : SpecTec.strtype) (rect : SpecTec.rectype) : SpecTec.strtype :=
  match strt with
  | .DefStructT st => .DefStructT (unrollStructtype st rect)
  | .DefArrayT arrayTy => .DefArrayT (unrollArraytype arrayTy rect)
  | .DefFuncT ft => .DefFuncT (unrollFunctype ft rect)

theorem subst_strtype_unroll_total (strt : SpecTec.strtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.strtype,
        SpecTec.Call.«$subst_strtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» strt⟩)
      start (.success (.of (unrollStrtype strt rect))) start := by
  cases strt with
  | DefStructT st =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_strtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefStructT st)))
        start (.success (.of (unrollStrtype (.DefStructT st) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_strtype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.DefStructT st))
        start (.success (.of (unrollStrtype (.DefStructT st) rect))) start
      unfold SpecTec.«$subst_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.Eval.bind_success
          (subst_structtype_unroll_total st rect start)
        exact SpecTecExecution.Eval.pure
          (SpecTec.strtype.DefStructT (unrollStructtype st rect))
  | DefArrayT arrayTy =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_strtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefArrayT arrayTy)))
        start (.success (.of (unrollStrtype (.DefArrayT arrayTy) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_strtype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefArrayT arrayTy)) start .unmatch start
        unfold SpecTec.«$subst_strtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_strtype:clause:1» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefArrayT arrayTy))
          start (.success (.of (unrollStrtype (.DefArrayT arrayTy) rect))) start
        unfold SpecTec.«$subst_strtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · apply SpecTecExecution.Eval.bind_success
            (subst_arraytype_unroll_total arrayTy rect start)
          exact SpecTecExecution.Eval.pure
            (SpecTec.strtype.DefArrayT (unrollArraytype arrayTy rect))
  | DefFuncT ft =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_strtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefFuncT ft)))
        start (.success (.of (unrollStrtype (.DefFuncT ft) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_strtype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.DefFuncT ft)) start .unmatch start
        unfold SpecTec.«$subst_strtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_strtype:clause:1» SpecTec.rectype rect
              SpecTec.Call.«$s_unroll» (.DefFuncT ft)) start .unmatch start
          unfold SpecTec.«$subst_strtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_strtype:clause:2» SpecTec.rectype rect
              SpecTec.Call.«$s_unroll» (.DefFuncT ft))
            start (.success (.of (unrollStrtype (.DefFuncT ft) rect))) start
          unfold SpecTec.«$subst_strtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
          · apply SpecTecExecution.Eval.bind_success
              (subst_functype_unroll_total ft rect start)
            exact SpecTecExecution.Eval.pure
              (SpecTec.strtype.DefFuncT (unrollFunctype ft rect))

theorem subst_strtype_unroll_deterministic (strt : SpecTec.strtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.strtype,
        SpecTec.Call.«$subst_strtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» strt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollStrtype strt rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_strtype_unroll_total strt rect start)

end properties.wasm_module_not_ok.Rejection
