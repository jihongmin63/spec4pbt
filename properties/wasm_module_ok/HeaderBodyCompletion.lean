import properties.wasm_module_ok.FuncHeadersStageGenerator
import properties.wasm_module_ok.UnreachableValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.HeaderBodyCompletion

def completedFunction (x : SpecTec.typeidx) : SpecTec.func :=
  { FTYPE := x, LOCALS := [], BODY := [.UNREACHABLE] }

theorem func_decl_result_types
    (c out : SpecTec.context) (f : SpecTec.func)
    (h : FuncDeclValidation.funcDeclResult c f = some out) :
    out.TYPES = c.TYPES := by
  unfold FuncDeclValidation.funcDeclResult at h
  cases hget : c.TYPES[f.FTYPE]? with
  | none => simp [hget] at h
  | some dt =>
      cases hft : UnrollInterface.deftypeFunctype dt with
      | none => simp [hget, hft] at h
      | some ft =>
          simp [hget, hft] at h
          cases h
          rfl

theorem func_decl_result_has_type
    (c out : SpecTec.context) (x : SpecTec.typeidx)
    (h : FuncDeclValidation.funcDeclResult c
      (FuncHeadersStageGenerator.headerFunction x) = some out) :
    ∃ ft, FunctionTypeValidation.funcTypeResult c x = some ft := by
  unfold FuncDeclValidation.funcDeclResult at h
  cases hget : c.TYPES[x]? with
  | none => simp [FuncHeadersStageGenerator.headerFunction, hget] at h
  | some dt =>
      cases hft : UnrollInterface.deftypeFunctype dt with
      | none =>
          simp [FuncHeadersStageGenerator.headerFunction,
            hget, hft] at h
      | some ft =>
          exact ⟨ft, by simp [FunctionTypeValidation.funcTypeResult,
            hget, hft]⟩

theorem func_type_result_eq_of_types
    (c d : SpecTec.context) (x : SpecTec.typeidx)
    (h : c.TYPES = d.TYPES) :
    FunctionTypeValidation.funcTypeResult c x =
      FunctionTypeValidation.funcTypeResult d x := by
  simp [FunctionTypeValidation.funcTypeResult, h]

theorem header_result_types
    (c out : SpecTec.context) (xs : List SpecTec.typeidx)
    (h : FuncHeadersStageGenerator.headerResult c xs = some out) :
    out.TYPES = c.TYPES := by
  induction xs generalizing c with
  | nil =>
      simp [FuncHeadersStageGenerator.headerResult,
        FuncsValidation.funcsResult] at h
      cases h
      rfl
  | cons x xs ih =>
      change (FuncDeclValidation.funcDeclResult c
        (FuncHeadersStageGenerator.headerFunction x)).bind
          (fun c₁ => FuncHeadersStageGenerator.headerResult c₁ xs) =
        some out at h
      cases hhead : FuncDeclValidation.funcDeclResult c
          (FuncHeadersStageGenerator.headerFunction x) with
      | none => simp [hhead] at h
      | some c₁ =>
          simp only [hhead, Option.bind_some] at h
          exact (ih c₁ h).trans (func_decl_result_types
            c c₁ (FuncHeadersStageGenerator.headerFunction x) hhead)

theorem header_member_has_type
    (c out : SpecTec.context) (xs : List SpecTec.typeidx)
    (h : FuncHeadersStageGenerator.headerResult c xs = some out)
    (x : SpecTec.typeidx) (hx : x ∈ xs) :
    ∃ ft, FunctionTypeValidation.funcTypeResult c x = some ft := by
  induction xs generalizing c with
  | nil => cases hx
  | cons head tail ih =>
      change (FuncDeclValidation.funcDeclResult c
        (FuncHeadersStageGenerator.headerFunction head)).bind
          (fun c₁ => FuncHeadersStageGenerator.headerResult c₁ tail) =
        some out at h
      cases hhead : FuncDeclValidation.funcDeclResult c
          (FuncHeadersStageGenerator.headerFunction head) with
      | none => simp [hhead] at h
      | some c₁ =>
          simp only [hhead, Option.bind_some] at h
          simp only [List.mem_cons] at hx
          cases hx with
          | inl heq =>
              subst x
              exact func_decl_result_has_type c c₁ head hhead
          | inr htail =>
              obtain ⟨ft, hft⟩ := ih c₁ h htail
              refine ⟨ft, ?_⟩
              rw [func_type_result_eq_of_types c c₁ x
                (func_decl_result_types c c₁
                  (FuncHeadersStageGenerator.headerFunction head)
                  hhead).symm]
              exact hft

theorem completed_body_total
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (ft : SpecTec.functype) (n : Nat)
    (hft : FunctionTypeValidation.funcTypeResult c x = some ft) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Funcbody_ok c
        (completedFunction x)⟩)
      n (.success (.of ())) n := by
  cases ft with
  | FuncT args results =>
      simpa [completedFunction,
        FuncHeadersStageGenerator.headerFunction] using
        (UnreachableValidation.funcbody_unreachable_total c
          (FuncHeadersStageGenerator.headerFunction x)
          args results n hft rfl)

theorem completed_bodies_of_types
    (c : SpecTec.context) (xs : List SpecTec.typeidx)
    (n : Nat)
    (hall : ∀ x ∈ xs,
      ∃ ft, FunctionTypeValidation.funcTypeResult c x = some ft) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Module_ok:rule:iter:2» c
        (xs.map completedFunction)⟩)
      n (.success (.of ())) n := by
  induction xs generalizing n with
  | nil =>
      exact FunctionBodyValidation.funcbody_iter_nil_success c n
  | cons x xs ih =>
      obtain ⟨ft, hft⟩ := hall x (by simp)
      apply (FunctionBodyValidation.funcbody_iter_cons_success_iff
        c (completedFunction x) (xs.map completedFunction) n n).2
      exact ⟨n, completed_body_total c x ft n hft,
        ih n (by
          intro y hy
          exact hall y (by simp [hy]))⟩

theorem completed_bodies_total
    (c out : SpecTec.context) (xs : List SpecTec.typeidx)
    (n : Nat)
    (h : FuncHeadersStageGenerator.headerResult c xs = some out) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Module_ok:rule:iter:2» c
        (xs.map completedFunction)⟩)
      n (.success (.of ())) n := by
  exact completed_bodies_of_types c xs n
    (fun x hx => header_member_has_type c out xs h x hx)

theorem completed_bodies_total_of_same_types
    (headerContext bodyContext out : SpecTec.context)
    (xs : List SpecTec.typeidx) (n : Nat)
    (h : FuncHeadersStageGenerator.headerResult
      headerContext xs = some out)
    (htypes : headerContext.TYPES = bodyContext.TYPES) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Module_ok:rule:iter:2»
        bodyContext (xs.map completedFunction)⟩)
      n (.success (.of ())) n := by
  apply completed_bodies_of_types bodyContext xs n
  intro x hx
  obtain ⟨ft, hft⟩ :=
    header_member_has_type headerContext out xs h x hx
  refine ⟨ft, ?_⟩
  rw [← func_type_result_eq_of_types
    headerContext bodyContext x htypes]
  exact hft

end properties.wasm_module_ok.HeaderBodyCompletion
