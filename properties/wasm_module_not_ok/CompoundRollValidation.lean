import properties.wasm_module_not_ok.FieldtypeListRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollStructtype (st : SpecTec.structtype) (x y : Nat) : SpecTec.structtype :=
  match st with
  | .StructT ys => .StructT (rollFieldtypes ys x y)

theorem subst_structtype_roll_total (st : SpecTec.structtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» st⟩)
      start (.success (.of (rollStructtype st x y))) start := by
  cases st with
  | StructT ys =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_structtype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.StructT ys)))
        start (.success (.of (rollStructtype (.StructT ys) x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_structtype:clause:0» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» (.StructT ys))
        start (.success (.of (rollStructtype (.StructT ys) x y))) start
      unfold SpecTec.«$subst_structtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_fieldtype_list_roll_total ys x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.structtype.StructT (rollFieldtypes ys x y))

def rollArraytype (arrayTy : SpecTec.arraytype) (x y : Nat) : SpecTec.arraytype :=
  match arrayTy with
  | .ArrayT yt => .ArrayT (rollFieldtype yt x y)

theorem subst_arraytype_roll_total (arrayTy : SpecTec.arraytype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» arrayTy⟩)
      start (.success (.of (rollArraytype arrayTy x y))) start := by
  cases arrayTy with
  | ArrayT yt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_arraytype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.ArrayT yt)))
        start (.success (.of (rollArraytype (.ArrayT yt) x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_arraytype:clause:0» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» (.ArrayT yt))
        start (.success (.of (rollArraytype (.ArrayT yt) x y))) start
      unfold SpecTec.«$subst_arraytype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_fieldtype_roll_total yt x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.arraytype.ArrayT (rollFieldtype yt x y))

theorem subst_structtype_roll_deterministic (st : SpecTec.structtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$subst_structtype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» st⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollStructtype st x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_structtype_roll_total st x y start)

theorem subst_arraytype_roll_deterministic (arrayTy : SpecTec.arraytype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» arrayTy⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollArraytype arrayTy x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_arraytype_roll_total arrayTy x y start)

end properties.wasm_module_not_ok.Rejection
