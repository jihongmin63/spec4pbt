import properties.wasm_module_ok.ConstructiveModuleFunctions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleFunctionList
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore

abbrev Ready (c : context) (xs : List Nat) := ∀x∈xs,(FunctionTypeValidation.funcTypeResult c x).isSome=true
structure Result (c : context) (xs : List Nat) where
  items : List SpecTec.func
  headers : items.map (·.FTYPE)=xs
  correct : ∀n,Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Module_ok:rule:iter:2» c items⟩) n (.success (.of ())) n

def done (c : context) : Result c [] := ⟨[],rfl,FunctionBodyValidation.funcbody_iter_nil_success c⟩
def cons (c : context) (x : Nat) (xs : List Nat) (f : ConstructiveModuleFunctions.Result c x) (tail : Result c xs) : Result c (x::xs) :=
  ⟨f.val::tail.items,by simp [f.property.1,tail.headers],fun n =>
    (FunctionBodyValidation.funcbody_iter_cons_success_iff c f.val tail.items n n).2
      ⟨n,f.property.2 n,tail.correct n⟩⟩

def generate (c : context) (env : Env c) : (xs : List Nat) → Ready c xs → Audited (Result c xs)
  | [],_ => Audited.pure (done c)
  | x::xs,hr =>
    (⟨ConstructiveModuleFunctions.generate c env x (hr x (by simp)),ConstructiveModuleFunctions.generate_audit c env x _⟩ : Audited _).bind fun f =>
      (generate c env xs (fun y hy => hr y (by simp [hy]))).map (cons c x xs f)

theorem complete (c : context) (env : Env c) (fs : List SpecTec.func) (hr : Ready c (fs.map (·.FTYPE)))
    (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Module_ok:rule:iter:2» c fs⟩) n (.success (.of ())) finish) :
    ∃out : Result c (fs.map (·.FTYPE)),Gen.support (generate c env _ hr).generator out ∧ out.items=fs := by
  induction fs generalizing n with
  | nil => exact ⟨done c,rfl,rfl⟩
  | cons f fs ih =>
    obtain ⟨middle,hf,ht⟩ := (FunctionBodyValidation.funcbody_iter_cons_success_iff c f fs n finish).1 h
    obtain ⟨head,hg,he⟩ := ConstructiveModuleFunctions.generate_complete c env f.FTYPE (hr f.FTYPE (by simp)) f rfl n middle hf
    obtain ⟨tail,hg',hs⟩ := ih (fun y hy => hr y (by simp [hy])) middle ht
    exact ⟨cons c f.FTYPE _ head tail,⟨head,hg,tail,hg',rfl⟩,by simp [cons,he,hs]⟩
#print axioms complete
end properties.wasm_module_ok.ConstructiveModuleFunctionList
