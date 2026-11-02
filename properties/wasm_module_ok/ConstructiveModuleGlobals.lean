import properties.wasm_module_ok.ConstructiveModuleInitializerPlans
import properties.wasm_module_ok.GlobalsDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleGlobals
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans

structure Step (c : context) where
  item : SpecTec.global
  after : context
  env : Env after
  correct : GlobalDecision.globalResult c item=some after

def step (c : context) (env : Env c) (p : Productive c env) (mu : SpecTec.mut)
    (code : Constant c p.1.val) : Step c where
  item := ⟨.GlobalT mu p.1.val,code.val⟩
  after := {c with GLOBALS:=c.GLOBALS++[.GlobalT mu p.1.val]}
  env := by
    apply ConstructiveModuleEnvironment.withGlobals c env
    intro gt hm
    rcases List.mem_append.mp hm with hm|hm
    · exact env.provenance.globals gt hm
    · have he : gt=.GlobalT mu p.1.val := by simpa using hm
      cases he; exact backed c p.1
  correct := by
    apply (GlobalDecision.global_result_iff_valid c _ _).2
    refine ⟨?_,rfl⟩
    have hc := (ConstExpressionDecision.constant_expression_result_iff_const_ok
      c p.1.val code.val 0 env.ready env.provenance env.nested (backed c p.1)).2 (code.property 0)
    simp [GlobalDecision.globalValid,GlobaltypeValidation.globaltypeValid,p.1.property,hc]

def constructors (c : context) (env : Env c) (round : Nat) : List (Audited (Step c)) :=
  (plans c env round).flatMap fun p =>
    [.Cons,.Var].map fun mu => (expressions c env p).map (step c env p mu)

structure Result (c : context) where
  items : List SpecTec.global
  after : context
  env : Env after
  correct : GlobalsDecision.globalsResult c items=some after

def done (c : context) (env : Env c) : Result c := ⟨[],c,env,rfl⟩
def cons (c : context) (head : Step c) (tail : Result head.after) : Result c :=
  ⟨head.item::tail.items,tail.after,tail.env,by
    simp only [GlobalsDecision.globalsResult,head.correct,Option.bind_some,tail.correct]⟩

/-- Each selected source-type plan supplies an executable initializer and the
next context. Future globals see precisely the preceding generated globals. -/
def sized : Nat → (c : context) → Env c → Audited (Result c)
  | 0,c,env => Audited.pure (done c env)
  | depth+1,c,env =>
    (⟨Gen.arbNat,ConstructiveGenAudit.arbNat_audit⟩ : Audited Nat).bind fun round =>
      (Audited.pure (done c env)).merge ((constructors c env round).map fun g =>
        g.bind fun head => (sized depth head.after head.env).map (cons c head))

def generate (c : context) (env : Env c) : Gen (Result c) :=
  Gen.arbNat >>= fun n => (sized n c env).generator

theorem generate_audit (c : context) (env : Env c) : ConstructiveGenAudit.Structural (generate c env) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => (sized n c env).audit⟩

theorem execute (c : context) (env : Env c) (out : Result c) (n : Nat) :
    SpecTecExecution.Eval specTecProgram (.call ⟨context,SpecTecCall.Globals_ok c out.items⟩)
      n (.success (.of out.after)) n :=
  (GlobalsDecision.globals_result_iff_call c out.after out.items n n env.ready env.provenance env.nested).1
    ⟨out.correct,rfl⟩

#print axioms execute
#print axioms generate_audit
end properties.wasm_module_ok.ConstructiveModuleGlobals
