import properties.wasm_module_ok.ConstructiveModuleInitializerPlans
import properties.wasm_module_ok.ConstructiveBodyCompleteness
import properties.wasm_module_ok.FuncbodyTrace
import properties.wasm_module_ok.ConstructiveLists
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleFunctionEnvironment
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore

abbrev Locals (c : context) := {ls : List SpecTec.local // LocalListValidation.allLocalsValid c ls=true}

def rawLocals (c : context) : Gen (List SpecTec.local) :=
  ConstructiveLists.all (SpecTec.local.mk <$> ConstructiveTypeAtoms.valtypes c)

theorem rawLocals_audit (c : context) : ConstructiveGenAudit.Structural (rawLocals c) :=
  ConstructiveLists.all_audit _ ((ConstructiveGenAudit.map_audit _ _).2
    (ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.valtypes_finite c)))

theorem rawLocals_exact (c : context) (ls : List SpecTec.local) :
    Gen.support (rawLocals c) ls ↔ LocalListValidation.allLocalsValid c ls=true := by
  induction ls with
  | nil => simp [rawLocals,LocalListValidation.allLocalsValid]
  | cons l ls ih =>
    cases l
    simp [rawLocals,LocalListValidation.allLocalsValid] at *
    exact fun _ => ih

def locals (c : context) : Audited (Locals c) :=
  ⟨ConstructiveAttach.refine (rawLocals c) (rawLocals_audit c) _
    (fun ls hl => (rawLocals_exact c ls).1 hl),ConstructiveAttach.refine_audit _ _ _ _⟩

theorem localTypes_backed (c : context) (ls : Locals c) :
    ∀ini t,localtype.LocalT ini t∈LocalListValidation.localTypes ls.val → CandidateValMatch.InTableVal c t := by
  intro ini t hm
  obtain ⟨l,hl,he⟩ := List.mem_map.mp hm
  have hv : ValtypeValidation.valtypeValid c l.LTYPE=true := by
    have hs := (rawLocals_exact c ls.val).2 ls.property
    rw [rawLocals,ConstructiveLists.all_support] at hs
    have hv := hs l hl
    obtain ⟨v,hv,he⟩ := hv
    cases l; cases he
    exact (ConstructiveTypeAtoms.support_valtypes c v).1 hv
  have ht : l.LTYPE=t := by
    unfold LocalValidation.localType at he
    split at he <;> cases he <;> rfl
  rw [←ht]
  exact (ConstructiveModuleInitializerPlans.backed c ⟨l.LTYPE,hv⟩)

theorem environment (c : context) (env : Env c) (x : Nat) (args results : List valtype)
    (hf : FunctionTypeValidation.funcTypeResult c x=some (.FuncT args results)) (ls : Locals c) :
    Env (FuncbodyTrace.bodyContext c args results (LocalListValidation.localTypes ls.val)) := by
  have hb := ConstructiveBodyBlocktypeCoverage.function_backed c env.nested x args results hf
  apply env.frame (FunctionBodyValidation.parameterLocals args++LocalListValidation.localTypes ls.val)
    [results] results
  · intro ini t hm
    rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨u,hu,he⟩ := List.mem_map.mp hm
      cases he; exact hb t (List.mem_append_left _ hu)
    · exact localTypes_backed c ls ini t hm
  · intro ts ht t hm
    have he : ts=results := by simpa using ht
    subst ts; exact hb t (List.mem_append_right _ hm)
  · intro t ht; exact hb t (List.mem_append_right _ ht)

theorem outputs (c : context) (env : Env c) (x : Nat) (args results : List valtype)
    (hf : FunctionTypeValidation.funcTypeResult c x=some (.FuncT args results)) (ls : Locals c) :
    ∀t∈results,CandidateValMatch.InTableVal
      (FuncbodyTrace.bodyContext c args results (LocalListValidation.localTypes ls.val)) t := by
  intro t ht
  exact CandidateProvenanceSteps.in_table_val_of_types_eq c _ t rfl
    (ConstructiveBodyBlocktypeCoverage.function_backed c env.nested x args results hf t (List.mem_append_right _ ht))

#print axioms environment
#print axioms rawLocals_exact
end properties.wasm_module_ok.ConstructiveModuleFunctionEnvironment
