import properties.wasm_module_not_ok.FieldtypeListUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollStructtype (st : SpecTec.structtype) (rect : SpecTec.rectype) : SpecTec.structtype :=
  match st with
  | .StructT ys => .StructT (unrollFieldtypes ys rect)

theorem subst_structtype_unroll_total (st : SpecTec.structtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» st⟩)
      start (.success (.of (unrollStructtype st rect))) start := by
  cases st with
  | StructT ys =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_structtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.StructT ys)))
        start (.success (.of (unrollStructtype (.StructT ys) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_structtype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.StructT ys))
        start (.success (.of (unrollStructtype (.StructT ys) rect))) start
      unfold SpecTec.«$subst_structtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_fieldtype_list_unroll_total ys rect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.structtype.StructT (unrollFieldtypes ys rect))

def unrollArraytype (arrayTy : SpecTec.arraytype) (rect : SpecTec.rectype) : SpecTec.arraytype :=
  match arrayTy with
  | .ArrayT yt => .ArrayT (unrollFieldtype yt rect)

theorem subst_arraytype_unroll_total (arrayTy : SpecTec.arraytype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» arrayTy⟩)
      start (.success (.of (unrollArraytype arrayTy rect))) start := by
  cases arrayTy with
  | ArrayT yt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_arraytype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.ArrayT yt)))
        start (.success (.of (unrollArraytype (.ArrayT yt) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_arraytype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.ArrayT yt))
        start (.success (.of (unrollArraytype (.ArrayT yt) rect))) start
      unfold SpecTec.«$subst_arraytype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_fieldtype_unroll_total yt rect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.arraytype.ArrayT (unrollFieldtype yt rect))

theorem subst_structtype_unroll_deterministic (st : SpecTec.structtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» st⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollStructtype st rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_structtype_unroll_total st rect start)

theorem subst_arraytype_unroll_deterministic (arrayTy : SpecTec.arraytype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» arrayTy⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollArraytype arrayTy rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_arraytype_unroll_total arrayTy rect start)

end properties.wasm_module_not_ok.Rejection
