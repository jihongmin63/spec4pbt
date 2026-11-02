import properties.wasm_module_ok.FunctionTypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncDeclValidation

def funcDeclResult (c : SpecTec.context)
    (f : SpecTec.func) : Option SpecTec.context :=
  match c.TYPES[f.FTYPE]? with
  | none => none
  | some dt =>
      match UnrollInterface.deftypeFunctype dt with
      | none => none
      | some _ => some { c with FUNCS := c.FUNCS ++ [dt] }

theorem func_ok_success_iff_result
    (c : SpecTec.context) (f : SpecTec.func)
    (result : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Func_ok c f⟩)
      n (.success (.of result)) finalSupply ↔
    funcDeclResult c f = some result ∧ finalSupply = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Func_ok:clause:0» c f)
          (fun _ => .unmatch))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Func_ok:clause:0» at hclause
        cases hclause with
        | bind_success htype htail =>
          rename_i middle ft
          obtain ⟨hfun, hsupply⟩ :=
            (FunctionTypeValidation.func_type_success_iff_result
              c f.FTYPE ft n middle).1 htype
          cases hsupply
          cases htail with
          | bind_success hbound htail =>
            cases hbound with
            | guard_true _ =>
              cases hget : c.TYPES[f.FTYPE]? with
              | none =>
                rw [hget] at htail
                cases htail
              | some dt =>
                rw [hget] at htail
                have hdt : UnrollInterface.deftypeFunctype dt = some ft := by
                  simpa [FunctionTypeValidation.funcTypeResult, hget] using hfun
                cases htail with
                | pure =>
                  exact ⟨by simp [funcDeclResult, hget, hdt], rfl⟩
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨hresult, rfl⟩
    cases hget : c.TYPES[f.FTYPE]? with
    | none => simp [funcDeclResult, hget] at hresult
    | some dt =>
      cases hft : UnrollInterface.deftypeFunctype dt with
      | none => simp [funcDeclResult, hget, hft] at hresult
      | some ft =>
        simp [funcDeclResult, hget, hft] at hresult
        cases hresult
        have hbound : f.FTYPE < c.TYPES.length :=
          (List.getElem?_eq_some_iff.mp hget).1
        have htype :=
          (FunctionTypeValidation.func_type_success_iff_result
            c f.FTYPE ft finalSupply finalSupply).2
            ⟨by simp [FunctionTypeValidation.funcTypeResult, hget, hft],
              rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses (SpecTec.Func_ok_clauses c f))
          finalSupply (.success (.of
            { c with FUNCS := c.FUNCS ++ [dt] })) finalSupply
        apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Func_ok:clause:0» c f)
          finalSupply (.success (.of
            { c with FUNCS := c.FUNCS ++ [dt] })) finalSupply
        unfold SpecTec.«Func_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success htype
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hbound
        · rw [hget]
          exact SpecTecExecution.Eval.pure
            { c with FUNCS := c.FUNCS ++ [dt] }

theorem func_ok_none (c : SpecTec.context)
    (f : SpecTec.func) (n : Nat)
    (hresult : funcDeclResult c f = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Func_ok c f⟩)
      n .unmatch n := by
  have hft : FunctionTypeValidation.funcTypeResult c f.FTYPE = none := by
    cases hget : c.TYPES[f.FTYPE]? with
    | none => simp [FunctionTypeValidation.funcTypeResult, hget]
    | some dt =>
      cases hdt : UnrollInterface.deftypeFunctype dt with
      | none =>
        simp [FunctionTypeValidation.funcTypeResult, hget, hdt]
      | some ft =>
        simp [funcDeclResult, hget, hdt] at hresult
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Func_ok_clauses c f))
    n .unmatch n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Func_ok:clause:0» c f) n .unmatch n
    unfold SpecTec.«Func_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact FunctionTypeValidation.func_type_none c f.FTYPE n hft
  · exact SpecTecExecution.tryClauses_nil n

def funcDeclOutcome (c : SpecTec.context) (f : SpecTec.func) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match funcDeclResult c f with
  | none => .unmatch
  | some result => .success (.of result)

theorem func_ok_total (c : SpecTec.context)
    (f : SpecTec.func) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Func_ok c f⟩)
      n (funcDeclOutcome c f) n := by
  cases hresult : funcDeclResult c f with
  | none =>
    simpa [funcDeclOutcome, hresult] using
      func_ok_none c f n hresult
  | some result =>
    simpa [funcDeclOutcome, hresult] using
      (func_ok_success_iff_result c f result n n).2
        ⟨hresult, rfl⟩

end properties.wasm_module_ok.FuncDeclValidation
