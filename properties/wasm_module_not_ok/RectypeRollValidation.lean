import properties.wasm_module_not_ok.SubtypeListRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollRectype (rect : SpecTec.rectype) (x y : Nat) : SpecTec.rectype :=
  match rect with
  | .RecT sts => .RecT (rollSubtypes sts x y)

theorem subst_rectype_roll_total (rect : SpecTec.rectype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» rect⟩)
      start (.success (.of (rollRectype rect x y))) start := by
  cases rect with
  | RecT sts =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_rectype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.RecT sts)) ())
        start (.success (.of (rollRectype (.RecT sts) x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_rectype:clause:0» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.RecT sts))
        start (.success (.of (rollRectype (.RecT sts) x y))) start
      unfold SpecTec.«$subst_rectype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_subtype_list_roll_total sts x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.rectype.RecT (rollSubtypes sts x y))

theorem subst_rectype_roll_deterministic (rect : SpecTec.rectype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» rect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollRectype rect x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_rectype_roll_total rect x y start)

def rollRectypeAt (x : Nat) (rect : SpecTec.rectype) : SpecTec.rectype :=
  match rect with
  | .RecT sts => rollRectype (.RecT sts) x (sts.length + x)

theorem rollrt_total (x : Nat) (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype, SpecTec.SpecTecCall.«$rollrt» x rect⟩)
      start (.success (.of (rollRectypeAt x rect))) start := by
  cases rect with
  | RecT sts =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$rollrt_clauses» x (.RecT sts)) ())
        start (.success (.of (rollRectypeAt x (.RecT sts)))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$rollrt:clause:0» x (.RecT sts))
        start (.success (.of (rollRectypeAt x (.RecT sts)))) start
      unfold SpecTec.«$rollrt:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_rectype_roll_total (.RecT sts) x (sts.length + x) start)
      exact SpecTecExecution.Eval.pure
        (rollRectype (.RecT sts) x (sts.length + x))

theorem rollrt_deterministic (x : Nat) (rect : SpecTec.rectype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype, SpecTec.SpecTecCall.«$rollrt» x rect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollRectypeAt x rect)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (rollrt_total x rect start)

end properties.wasm_module_not_ok.Rejection
