import properties.wasm_module_not_ok.MatchFieldtypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def strtypeKind : SpecTec.strtype → Nat
  | .DefStructT _ => 0
  | .DefArrayT _ => 1
  | .DefFuncT _ => 2

theorem match_strtype_struct_array_false (d : List SpecTec.deftype)
    (x : SpecTec.structtype) (y : SpecTec.arraytype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefStructT x) (.DefArrayT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefStructT x) (.DefArrayT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefStructT x) (.DefArrayT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefStructT x) (.DefArrayT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefStructT x) (.DefArrayT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefStructT x) (.DefArrayT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_struct_func_false (d : List SpecTec.deftype)
    (x : SpecTec.structtype) (y : SpecTec.functype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefStructT x) (.DefFuncT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefStructT x) (.DefFuncT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefStructT x) (.DefFuncT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefStructT x) (.DefFuncT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefStructT x) (.DefFuncT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefStructT x) (.DefFuncT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_array_struct_false (d : List SpecTec.deftype)
    (x : SpecTec.arraytype) (y : SpecTec.structtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefArrayT x) (.DefStructT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefArrayT x) (.DefStructT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefArrayT x) (.DefStructT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefArrayT x) (.DefStructT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefArrayT x) (.DefStructT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefArrayT x) (.DefStructT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_array_func_false (d : List SpecTec.deftype)
    (x : SpecTec.arraytype) (y : SpecTec.functype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefArrayT x) (.DefFuncT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefArrayT x) (.DefFuncT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefArrayT x) (.DefFuncT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefArrayT x) (.DefFuncT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefArrayT x) (.DefFuncT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefArrayT x) (.DefFuncT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_func_struct_false (d : List SpecTec.deftype)
    (x : SpecTec.functype) (y : SpecTec.structtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefFuncT x) (.DefStructT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefFuncT x) (.DefStructT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefFuncT x) (.DefStructT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefFuncT x) (.DefStructT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefFuncT x) (.DefStructT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
        · apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefFuncT x) (.DefStructT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_func_array_false (d : List SpecTec.deftype)
    (x : SpecTec.functype) (y : SpecTec.arraytype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefFuncT x) (.DefArrayT y)⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses» d (.DefFuncT x) (.DefArrayT y)) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d (.DefFuncT x) (.DefArrayT y))
      start .unmatch start
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:strtype:DefStructT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d (.DefFuncT x) (.DefArrayT y))
        start .unmatch start
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d (.DefFuncT x) (.DefArrayT y))
          start .unmatch start
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
        · apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:3» d (.DefFuncT x) (.DefArrayT y))
          start (.success (.of false)) start
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_mixed_false (d : List SpecTec.deftype)
    (a b : SpecTec.strtype) (start : Nat)
    (hkind : strtypeKind a ≠ strtypeKind b) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d a b⟩)
      start (.success (.of false)) start := by
  cases a with
  | DefStructT x =>
      cases b with
      | DefStructT y => simp [strtypeKind] at hkind
      | DefArrayT y => exact match_strtype_struct_array_false d x y start
      | DefFuncT y => exact match_strtype_struct_func_false d x y start
  | DefArrayT x =>
      cases b with
      | DefStructT y => exact match_strtype_array_struct_false d x y start
      | DefArrayT y => simp [strtypeKind] at hkind
      | DefFuncT y => exact match_strtype_array_func_false d x y start
  | DefFuncT x =>
      cases b with
      | DefStructT y => exact match_strtype_func_struct_false d x y start
      | DefArrayT y => exact match_strtype_func_array_false d x y start
      | DefFuncT y => simp [strtypeKind] at hkind

theorem match_strtype_mixed_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.strtype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (hkind : strtypeKind a ≠ strtypeKind b)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d a b⟩)
      start outcome finalSupply) :
    outcome = .success (.of false) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_strtype_mixed_false d a b start hkind)

end properties.wasm_module_not_ok.Rejection
