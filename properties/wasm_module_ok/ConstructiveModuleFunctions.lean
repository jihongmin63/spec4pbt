import properties.wasm_module_ok.ConstructiveModuleFunctionEnvironment
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleFunctions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleFunctionEnvironment

abbrev Signature (c : context) (x : Nat) :=
  {ft : functype // FunctionTypeValidation.funcTypeResult c x=some ft}
def signature (c : context) (x : Nat) (hf : (FunctionTypeValidation.funcTypeResult c x).isSome=true) : Signature c x :=
  match he : FunctionTypeValidation.funcTypeResult c x with
  | some ft => ⟨ft,he⟩
  | none => False.elim (by simp [he] at hf)

abbrev Result (c : context) (x : Nat) :=
  {f : SpecTec.func // f.FTYPE=x ∧ ∀n,SpecTecExecution.Eval Body
    (.call ⟨Unit,Call.Funcbody_ok c f⟩) n (.success (.of ())) n}

def finish (c : context) (env : Env c) (x : Nat) (args results : List valtype)
    (hf : FunctionTypeValidation.funcTypeResult c x=some (.FuncT args results)) (ls : Locals c)
    (body : ConstructiveBodyControlProductions.Body
      (FuncbodyTrace.bodyContext c args results (LocalListValidation.localTypes ls.val)) [] results) : Result c x :=
  ⟨⟨x,ls.val,body.val⟩,rfl,fun n => (FuncbodyTrace.funcbody_success_iff_precomputed c _ n n).2
    ⟨args,results,hf,ls.property,body.property n⟩⟩

def withLocals (c : context) (env : Env c) (x : Nat) (args results : List valtype)
    (hf : FunctionTypeValidation.funcTypeResult c x=some (.FuncT args results)) (ls : Locals c) : Audited (Result c x) :=
  let d := FuncbodyTrace.bodyContext c args results (LocalListValidation.localTypes ls.val)
  let ed := environment c env x args results hf ls
  let hi : ∀t∈([] : List valtype),CandidateValMatch.InTableVal d t := by simp
  let ho := outputs c env x args results hf ls
  (⟨ConstructiveBodyGeneration.generate d ed [] results hi ho,
    ConstructiveBodyGeneration.generate_audit d ed [] results hi ho⟩ : Audited _).map
    (finish c env x args results hf ls)

def fromSignature (c : context) (env : Env c) (x : Nat) (s : Signature c x) : Audited (Result c x) :=
  match s with
  | ⟨.FuncT args results,hf⟩ =>
    (locals c).bind (withLocals c env x args results hf)

def generate (c : context) (env : Env c) (x : Nat)
    (hf : (FunctionTypeValidation.funcTypeResult c x).isSome=true) : Gen (Result c x) :=
  (fromSignature c env x (signature c x hf)).generator

theorem generate_audit (c : context) (env : Env c) (x : Nat)
    (hf : (FunctionTypeValidation.funcTypeResult c x).isSome=true) : ConstructiveGenAudit.Structural (generate c env x hf) :=
  (fromSignature c env x (signature c x hf)).audit

theorem fromSignature_complete (c : context) (env : Env c) (x : Nat) (s : Signature c x)
    (f : SpecTec.func) (hx : f.FTYPE=x) (start endSupply : Nat)
    (h : SpecTecExecution.Eval Body (.call ⟨Unit,Call.Funcbody_ok c f⟩)
      start (.success (.of ())) endSupply) :
    ∃out : Result c x,Gen.support (fromSignature c env x s).generator out ∧ out.val=f := by
  obtain ⟨args,results,hf,hl,hbody⟩ := (FuncbodyTrace.funcbody_success_iff_precomputed c f start endSupply).1 h
  rw [hx] at hf
  rcases s with ⟨⟨args',results'⟩,hs⟩
  have he : functype.FuncT args results=.FuncT args' results' := Option.some.inj (hf.symm.trans hs)
  cases he
  let ls : Locals c := ⟨f.LOCALS,hl⟩
  have hls : Gen.support (locals c).generator ls := by
    rw [locals,ConstructiveAttach.refine_support,rawLocals_exact];exact hl
  have hb := (ConstructiveBodyCompleteness.bodies_complete _
    (environment c env x args results hf ls) [] results (by simp)
    (outputs c env x args results hf ls) f.BODY start endSupply hbody).1
  obtain ⟨body,hg,hcode⟩ := hb
  refine ⟨finish c env x args results hf ls body,⟨ls,hls,body,hg,rfl⟩,?_⟩
  cases f
  simp_all [finish,ls]

theorem generate_complete (c : context) (env : Env c) (x : Nat)
    (hf : (FunctionTypeValidation.funcTypeResult c x).isSome=true)
    (f : SpecTec.func) (hx : f.FTYPE=x) (start endSupply : Nat)
    (h : SpecTecExecution.Eval Body (.call ⟨Unit,Call.Funcbody_ok c f⟩)
      start (.success (.of ())) endSupply) :
    ∃out : Result c x,Gen.support (generate c env x hf) out ∧ out.val=f :=
  fromSignature_complete c env x (signature c x hf) f hx start endSupply h

#print axioms generate_complete
#print axioms generate_audit
end properties.wasm_module_ok.ConstructiveModuleFunctions
