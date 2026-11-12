import properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyLocalCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodySimpleAtoms ConstructiveBodyEvalReduction

theorem get_lookup (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.GET» x)⟩)
      n (.success (.of effect)) finish) : ∃t,c.LOCALS[x]?=some (.LocalT .Set t) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.GET» x) 25 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:25» c stack (.«LOCAL.GET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:25» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.LOCALS[x]? with
  | none => rw [hx] at hs; cases hs
  | some value =>
    cases value with | LocalT ini t =>
      simp only [hx] at hs
      obtain ⟨hi,_⟩ := (bind_guard _ _ _ _ _).1 hs
      cases ini with
      | Unset => cases hi
      | Set => exact ⟨t,rfl⟩

theorem set_lookup (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.SET» x)⟩)
      n (.success (.of effect)) finish) : ∃ini t,c.LOCALS[x]?=some (.LocalT ini t) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.SET» x) 26 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:26» c stack (.«LOCAL.SET» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:26» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨hb,_⟩ := (bind_guard _ _ _ _ _).1 hs
  cases he : c.LOCALS[x] with | LocalT ini t =>
    exact ⟨ini,t,by simpa only [he] using List.getElem?_eq_getElem hb⟩

theorem tee_lookup (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.TEE» x)⟩)
      n (.success (.of effect)) finish) : ∃ini t,c.LOCALS[x]?=some (.LocalT ini t) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.TEE» x) 27 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:27» c stack (.«LOCAL.TEE» x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:27» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨hb,_⟩ := (bind_guard _ _ _ _ _).1 hs
  cases he : c.LOCALS[x] with | LocalT ini t =>
    exact ⟨ini,t,by simpa only [he] using List.getElem?_eq_getElem hb⟩

theorem get_mem (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (t : valtype)
    (hx : c.LOCALS[x]?=some (.LocalT .Set t)) : localGet c stack env x t hx∈locals c stack env := by
  obtain ⟨hb,hget⟩ := List.getElem?_eq_some_iff.mp hx
  apply List.mem_flatMap.mpr
  refine ⟨⟨x,hb⟩,by simp,?_⟩
  simp only [hget]
  apply List.mem_append_right
  have hi : c.LOCALS[x].1=init.Set := by rw [hget]
  split
  next he => exact List.mem_singleton_self _
  next he =>
    have hu : c.LOCALS[x].1=init.Unset := by assumption
    have hh : init.Set=init.Unset := hi.symm.trans hu
    cases hh

theorem write_mem (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (ini : init) (t : valtype)
    (hx : c.LOCALS[x]?=some (.LocalT ini t)) (tee : Bool) : localWrite c stack env x ini t hx tee∈locals c stack env := by
  obtain ⟨hb,hget⟩ := List.getElem?_eq_some_iff.mp hx
  apply List.mem_flatMap.mpr
  refine ⟨⟨x,hb⟩,by simp,?_⟩
  simp only [hget]
  apply List.mem_append_left
  cases tee <;> simp

theorem get_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.GET» x)⟩)
      n (.success (.of effect)) finish) : Covers (locals c stack env) (.«LOCAL.GET» x) effect ∧ finish=n := by
  obtain ⟨t,hx⟩ := get_lookup c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (locals c stack env) (localGet c stack env x t hx) _ effect n finish
    (get_mem c stack env x t hx) _ h
  exact ⟨_,rfl,rfl⟩

theorem set_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.SET» x)⟩)
      n (.success (.of effect)) finish) : Covers (locals c stack env) (.«LOCAL.SET» x) effect ∧ finish=n := by
  obtain ⟨ini,t,hx⟩ := set_lookup c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (locals c stack env) (localWrite c stack env x ini t hx false) _ effect n finish
    (write_mem c stack env x ini t hx false) _ h
  exact ⟨_,rfl,rfl⟩

theorem tee_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«LOCAL.TEE» x)⟩)
      n (.success (.of effect)) finish) : Covers (locals c stack env) (.«LOCAL.TEE» x) effect ∧ finish=n := by
  obtain ⟨ini,t,hx⟩ := tee_lookup c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (locals c stack env) (localWrite c stack env x ini t hx true) _ effect n finish
    (write_mem c stack env x ini t hx true) _ h
  exact ⟨_,rfl,rfl⟩

#print axioms get_original
#print axioms tee_original
end properties.wasm_module_ok.ConstructiveBodyLocalCoverage
