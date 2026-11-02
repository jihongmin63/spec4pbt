import properties.wasm_module_ok.ImportsValidation
import properties.wasm_module_ok.FuncsValidation
import properties.wasm_module_ok.MemsValidation
import properties.wasm_module_ok.TagsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ContextRefsValidation

theorem import_decl_refs (c result : SpecTec.context)
    (i : SpecTec.«import»)
    (h : ImportValidation.importDeclResult c i = some result) :
    result.REFS = c.REFS := by
  unfold ImportValidation.importDeclResult
    ImportValidation.funcImportResult
    ImportValidation.tagImportResult at h
  split at h <;> repeat (split at h) <;> simp_all
  all_goals
    first
    | simpa using (congrArg SpecTec.context.REFS h).symm
    | simpa using (congrArg SpecTec.context.REFS h.2).symm

theorem func_decl_refs (c result : SpecTec.context)
    (f : SpecTec.func)
    (h : FuncDeclValidation.funcDeclResult c f = some result) :
    result.REFS = c.REFS := by
  cases hlookup : c.TYPES[f.FTYPE]? with
  | none => simp [FuncDeclValidation.funcDeclResult, hlookup] at h
  | some dt =>
      cases hfun : UnrollInterface.deftypeFunctype dt with
      | none => simp [FuncDeclValidation.funcDeclResult, hlookup, hfun] at h
      | some ft =>
          simp [FuncDeclValidation.funcDeclResult, hlookup, hfun] at h
          cases h
          rfl

theorem mem_decl_refs (c result : SpecTec.context)
    (m : SpecTec.memory)
    (h : MemsValidation.memDeclResult c m = some result) :
    result.REFS = c.REFS := by
  unfold MemsValidation.memDeclResult at h
  split at h <;> simp_all
  simpa using (congrArg SpecTec.context.REFS h).symm

theorem imports_result_refs (c result : SpecTec.context)
    (is : List SpecTec.«import»)
    (h : ImportsValidation.importsResult c is = some result) :
    result.REFS = c.REFS := by
  induction is generalizing c with
  | nil =>
      simp [ImportsValidation.importsResult] at h
      cases h
      rfl
  | cons i rest ih =>
      simp only [ImportsValidation.importsResult] at h
      cases hstep : ImportValidation.importDeclResult c i with
      | none => simp [hstep] at h
      | some c₁ =>
          simp [hstep] at h
          exact (ih c₁ h).trans (import_decl_refs c c₁ i hstep)

theorem funcs_result_refs (c result : SpecTec.context)
    (fs : List SpecTec.func)
    (h : FuncsValidation.funcsResult c fs = some result) :
    result.REFS = c.REFS := by
  induction fs generalizing c with
  | nil =>
      simp [FuncsValidation.funcsResult] at h
      cases h
      rfl
  | cons f rest ih =>
      simp only [FuncsValidation.funcsResult] at h
      cases hstep : FuncDeclValidation.funcDeclResult c f with
      | none => simp [hstep] at h
      | some c₁ =>
          simp [hstep] at h
          exact (ih c₁ h).trans (func_decl_refs c c₁ f hstep)

theorem mems_result_refs (c result : SpecTec.context)
    (ms : List SpecTec.memory)
    (h : MemsValidation.memsResult c ms = some result) :
    result.REFS = c.REFS := by
  induction ms generalizing c with
  | nil =>
      simp [MemsValidation.memsResult] at h
      cases h
      rfl
  | cons m rest ih =>
      simp only [MemsValidation.memsResult] at h
      cases hstep : MemsValidation.memDeclResult c m with
      | none => simp [hstep] at h
      | some c₁ =>
          simp [hstep] at h
          exact (ih c₁ h).trans (mem_decl_refs c c₁ m hstep)

theorem imports_ok_refs (c result : SpecTec.context)
    (is : List SpecTec.«import») (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok c is⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS :=
  imports_result_refs c result is
    ((ImportsValidation.imports_success_iff_result
      c is result n finalSupply).mp hcall).1

theorem funcs_ok_refs (c result : SpecTec.context)
    (fs : List SpecTec.func) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Funcs_ok c fs⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS :=
  funcs_result_refs c result fs
    ((FuncsValidation.funcs_success_iff_result
      c fs result n finalSupply).mp hcall).1

theorem mems_ok_refs (c result : SpecTec.context)
    (ms : List SpecTec.memory) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Mems_ok c ms⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS :=
  mems_result_refs c result ms
    ((MemsValidation.mems_success_iff_result
      c ms result n finalSupply).mp hcall).1

theorem tag_decl_refs (c result : SpecTec.context)
    (t : SpecTec.tag)
    (h : TagsValidation.tagDeclResult c t = some result) :
    result.REFS = c.REFS := by
  cases hlookup : c.TYPES[t.TGTYPE]? with
  | none => simp [TagsValidation.tagDeclResult, hlookup] at h
  | some dt =>
      cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false => simp [TagsValidation.tagDeclResult, hlookup, hv] at h
      | true =>
          simp [TagsValidation.tagDeclResult, hlookup, hv] at h
          cases h
          rfl

theorem tags_result_refs (c result : SpecTec.context)
    (ts : List SpecTec.tag)
    (h : TagsValidation.tagsResult c ts = some result) :
    result.REFS = c.REFS := by
  induction ts generalizing c with
  | nil =>
      simp [TagsValidation.tagsResult] at h
      cases h
      rfl
  | cons t rest ih =>
      simp only [TagsValidation.tagsResult] at h
      cases hstep : TagsValidation.tagDeclResult c t with
      | none => simp [hstep] at h
      | some c₁ =>
          simp [hstep] at h
          exact (ih c₁ h).trans (tag_decl_refs c c₁ t hstep)

theorem tags_ok_refs (c result : SpecTec.context)
    (ts : List SpecTec.tag) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS :=
  tags_result_refs c result ts
    ((TagsValidation.tags_success_iff_result
      c ts result n finalSupply).mp hcall).1

end properties.wasm_module_ok.ContextRefsValidation
