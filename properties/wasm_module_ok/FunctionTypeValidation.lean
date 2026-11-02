import properties.wasm_module_ok.StartValidation
import properties.wasm_module_ok.UnrollInterface
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FunctionTypeValidation

theorem func_type_success_iff
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (ft : SpecTec.functype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype, SpecTec.Call.«$func_type» c x⟩)
      n (.success (.of ft)) finalSupply ↔
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.strtype, SpecTec.Call.«$expanddt» dt⟩)
        n (.success (.of (SpecTec.strtype.DefFuncT ft))) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«$func_type:clause:0» c x)
          (fun _ => .unmatch))
        n (.success (.of ft)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$func_type:clause:0» at hclause
        cases hclause with
        | bind_success hbound htail =>
          cases hbound with
          | guard_true _ =>
            cases hget : c.TYPES[x]? with
            | none =>
              rw [hget] at htail
              cases htail
            | some dt =>
              rw [hget] at htail
              cases htail with
              | bind_success hexpand htail =>
                rename_i middle strt
                cases htail with
                | bind_success hshape htail =>
                  cases hshape with
                  | guard_true hcond =>
                    cases strt with
                    | DefStructT _ =>
                      simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
                    | DefArrayT _ =>
                      simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
                    | DefFuncT ft' =>
                      cases htail with
                      | pure => exact ⟨dt, rfl, hexpand⟩
      | orElse_unmatch hfailedSupply hlast => restore_supply hfailedSupply at hlast; cases hlast
  · rintro ⟨dt, hget, hexpand⟩
    have hindex : x < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$func_type_clauses» c x))
      n (.success (.of ft)) finalSupply
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$func_type:clause:0» c x)
      n (.success (.of ft)) finalSupply
    unfold SpecTec.«$func_type:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      exact hindex
    · rw [hget]
      apply SpecTecExecution.Eval.bind_success hexpand
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · exact SpecTecExecution.Eval.pure ft

theorem func_type_success_iff_unrolldt
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (ft : SpecTec.functype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype, SpecTec.Call.«$func_type» c x⟩)
      n (.success (.of ft)) finalSupply ↔
    ∃ (dt : SpecTec.deftype) (fin : SpecTec.final)
      (supers : List SpecTec.heaptype),
      c.TYPES[x]? = some dt ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.subtype, SpecTec.Call.«$unrolldt» dt⟩)
        n (.success (.of (SpecTec.subtype.SubT fin supers
          (SpecTec.strtype.DefFuncT ft)))) finalSupply := by
  rw [func_type_success_iff]
  constructor
  · rintro ⟨dt, hget, hexpand⟩
    obtain ⟨fin, supers, hunroll⟩ :=
      (StartValidation.expanddt_success_iff_unrolldt
        dt (.DefFuncT ft) n finalSupply).1 hexpand
    exact ⟨dt, fin, supers, hget, hunroll⟩
  · rintro ⟨dt, fin, supers, hget, hunroll⟩
    exact ⟨dt, hget,
      (StartValidation.expanddt_success_iff_unrolldt
        dt (.DefFuncT ft) n finalSupply).2 ⟨fin, supers, hunroll⟩⟩

def funcTypeResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.functype :=
  match c.TYPES[x]? with
  | some dt => UnrollInterface.deftypeFunctype dt
  | none => none

theorem func_type_success_iff_result
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (ft : SpecTec.functype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype, SpecTec.Call.«$func_type» c x⟩)
      n (.success (.of ft)) finalSupply ↔
    funcTypeResult c x = some ft ∧ finalSupply = n := by
  rw [func_type_success_iff_unrolldt]
  constructor
  · rintro ⟨dt, fin, supers, hget, hunroll⟩
    obtain ⟨hft, hsupply⟩ :=
      (UnrollInterface.unroll_functype_success_iff
        dt ft n finalSupply).1 ⟨fin, supers, hunroll⟩
    exact ⟨by simp [funcTypeResult, hget, hft], hsupply⟩
  · rintro ⟨hresult, hsupply⟩
    cases hget : c.TYPES[x]? with
    | none => simp [funcTypeResult, hget] at hresult
    | some dt =>
      have hft : UnrollInterface.deftypeFunctype dt = some ft := by
        simpa [funcTypeResult, hget] using hresult
      obtain ⟨fin, supers, hunroll⟩ :=
        (UnrollInterface.unroll_functype_success_iff
          dt ft n finalSupply).2 ⟨hft, hsupply⟩
      exact ⟨dt, fin, supers, rfl, hunroll⟩

def funcTypeOutcome (c : SpecTec.context) (x : SpecTec.typeidx) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match funcTypeResult c x with
  | none => .unmatch
  | some ft => .success (.of ft)

theorem func_type_none (c : SpecTec.context)
    (x : SpecTec.typeidx) (n : Nat)
    (hresult : funcTypeResult c x = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$func_type» c x⟩)
      n .unmatch n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$func_type_clauses» c x))
    n .unmatch n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$func_type:clause:0» c x) n .unmatch n
    unfold SpecTec.«$func_type:clause:0»
    cases hget : c.TYPES[x]? with
    | none =>
      have hbound : ¬ x < c.TYPES.length :=
        Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hget)
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false hbound
    | some dt =>
      have hbound : x < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hget).1
      apply SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true hbound)
      rw [hget]
      cases hunroll : properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt with
      | none =>
        apply SpecTecExecution.Eval.bind_unmatch
        simpa [UnrollInterface.expandOutcome,
          UnrollInterface.expandResult, hunroll] using
          UnrollInterface.expanddt_total dt n
      | some subtype =>
        cases subtype with
        | SubT fin supers strt =>
          cases strt with
          | DefFuncT ft =>
            simp [funcTypeResult, hget, UnrollInterface.deftypeFunctype,
              hunroll] at hresult
          | DefStructT st =>
            apply SpecTecExecution.Eval.bind_success
            · simpa [UnrollInterface.expandOutcome,
                UnrollInterface.expandResult, hunroll] using
                UnrollInterface.expanddt_total dt n
            · apply SpecTecExecution.Eval.bind_unmatch
              apply SpecTecExecution.Eval.guard_false
              simp [SpecTec.«exec:match:strtype:DefFuncT»]
          | DefArrayT arr =>
            apply SpecTecExecution.Eval.bind_success
            · simpa [UnrollInterface.expandOutcome,
                UnrollInterface.expandResult, hunroll] using
                UnrollInterface.expanddt_total dt n
            · apply SpecTecExecution.Eval.bind_unmatch
              apply SpecTecExecution.Eval.guard_false
              simp [SpecTec.«exec:match:strtype:DefFuncT»]
  · exact SpecTecExecution.tryClauses_nil n

theorem func_type_total (c : SpecTec.context)
    (x : SpecTec.typeidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$func_type» c x⟩)
      n (funcTypeOutcome c x) n := by
  cases hresult : funcTypeResult c x with
  | none =>
    simpa [funcTypeOutcome, hresult] using
      func_type_none c x n hresult
  | some ft =>
    simpa [funcTypeOutcome, hresult] using
      (func_type_success_iff_result c x ft n n).2
        ⟨hresult, rfl⟩

theorem func_type_deterministic (c : SpecTec.context)
    (x : SpecTec.typeidx) (n finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$func_type» c x⟩)
      n outcome finalSupply) :
    outcome = funcTypeOutcome c x ∧ finalSupply = n := by
  exact properties.wasm_module_ok.Execution.eval_deterministic h
    (func_type_total c x n)

end properties.wasm_module_ok.FunctionTypeValidation
