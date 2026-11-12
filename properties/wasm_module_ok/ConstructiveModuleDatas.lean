import properties.wasm_module_ok.ConstructiveModuleDataStep
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleDatas
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore ConstructiveModuleDataStep

structure Result (c : context) where
  items : List SpecTec.data
  after : context
  env : Env after
  correct : ∀n,Eval Body (.call ⟨context,Call.Datas_ok c items⟩) n (.success (.of after)) n

def done (c : context) (env : Env c) : Result c := ⟨[],c,env,EmptyStageValidation.datas_nil_total c⟩
def cons (c : context) (head : Step c) (tail : Result head.after) : Result c :=
  ⟨head.item::tail.items,tail.after,tail.env,fun n => ConstructiveModuleElemDataRules.datas_cons c head.after tail.after
    head.item tail.items n n n (head.correct n) (tail.correct n)⟩
def sized : Nat → (c : context) → Env c → Audited (Result c)
  | 0,c,env => Audited.pure (done c env)
  | n+1,c,env => (one c env).bind fun head =>
      (sized n head.after head.env).map (cons c head)
def generate (c : context) (env : Env c) : Gen (Result c) := Gen.arbNat >>= fun n => (sized n c env).generator

theorem generate_audit (c : context) (env : Env c) : ConstructiveGenAudit.Structural (generate c env) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => (sized n c env).audit⟩

theorem sized_complete (c result : context) (env : Env c) (xs : List SpecTec.data) (start finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c xs⟩) start (.success (.of result)) finish) :
    ∃out : Result c,Gen.support (sized xs.length c env).generator out ∧ out.items=xs ∧ out.after=result := by
  induction xs generalizing c start finish with
  | nil => exact ⟨done c env,rfl,rfl,(ConstructiveModuleElemDataRules.datas_nil c result start finish h).1.symm⟩
  | cons x xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := ConstructiveModuleElemDataRules.datas_original c result x xs start finish h
    obtain ⟨head,hg,he,ho⟩ := ConstructiveModuleDataStep.complete c next env x start middle hh
    rw [←ho] at ht
    obtain ⟨tail,hg',hs,hout⟩ := ih head.after head.env middle finish ht
    exact ⟨cons c head tail,⟨head,hg,tail,hg',rfl⟩,by simp [cons,he,hs],hout⟩

theorem generate_complete (c result : context) (env : Env c) (xs : List SpecTec.data) (start finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c xs⟩) start (.success (.of result)) finish) :
    ∃out : Result c,Gen.support (generate c env) out ∧ out.items=xs ∧ out.after=result := by
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result env xs start finish h
  exact ⟨out,⟨xs.length,by simp,hg⟩,hs,ho⟩
#print axioms generate_complete
end properties.wasm_module_ok.ConstructiveModuleDatas
