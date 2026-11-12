import properties.wasm_module_ok.ConstructiveModuleInitializerPlans
import properties.wasm_module_ok.TablesDecision
import properties.wasm_module_ok.ConstructiveLimits
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleTables
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans

def bound : addrtype → Nat | .I32AT => 4294967295 | .I64AT => 18446744073709551615
abbrev Extent (addr : addrtype) := {lim : SpecTec.limits // LimitsValidation.limitsValid (bound addr) lim=true}
def extents (addr : addrtype) : Audited (Extent addr) :=
  ⟨ConstructiveAttach.refine (ConstructiveLimits.limits (bound addr))
    (ConstructiveGenAudit.finite_audit _ (ConstructiveLimits.limits_finite _)) _
    (fun lim hl => (ConstructiveLimits.limits_support _ _).1 hl),ConstructiveAttach.refine_audit _ _ _ _⟩

structure Step (c : context) where
  item : SpecTec.table
  after : context
  env : Env after
  correct : TableDecision.tableResult c item=some after

def step (c : context) (env : Env c) (p : Productive c env) (rt : reftype)
    (he : p.1.val=.RefT rt) (addr : addrtype) (lim : Extent addr)
    (code : Constant c p.1.val) : Step c where
  item := ⟨.TableT addr lim.val rt,code.val⟩
  after := {c with TABLES:=c.TABLES++[.TableT addr lim.val rt]}
  env := by
    apply ConstructiveModuleEnvironment.withTables c env
    intro a l r hm
    rcases List.mem_append.mp hm with hm|hm
    · exact env.tables a l r hm
    · have hh : tabletype.TableT a l r=.TableT addr lim.val rt := by simpa using hm
      cases hh; simpa only [he] using backed c p.1
  correct := by
    apply (TableDecision.table_result_iff_valid c _ _).2
    refine ⟨?_,rfl⟩
    have hv := p.1.property
    rw [he] at hv
    have hc := (ConstExpressionDecision.constant_expression_result_iff_const_ok
      c p.1.val code.val 0 env.ready env.provenance env.nested (backed c p.1)).2 (code.property 0)
    simp only [he] at hc
    have hl := lim.property
    cases addr <;> cases rt <;>
      simpa [TableDecision.tableValid,TabletypeValidation.tabletypeValid,
        ReftypeTotal.reftypeValid,ValtypeValidation.valtypeValid,bound,hc] using And.intro hv hl

def branch (c : context) (env : Env c) (p : Productive c env) (rt : reftype)
    (he : p.1.val=.RefT rt) (addr : addrtype) : Audited (Step c) :=
  (extents addr).bind fun lim => (expressions c env p).map (step c env p rt he addr lim)

/-- Only reference source types receive table constructors. Bounds are built
structurally, and the selected initializer plan is productive before sampling. -/
def constructors (c : context) (env : Env c) (round : Nat) : List (Audited (Step c)) :=
  (plans c env round).flatMap fun p =>
    match he : p.1.val with
    | .RefT rt => [branch c env p rt he .I32AT,branch c env p rt he .I64AT]
    | _ => []

structure Result (c : context) where
  items : List SpecTec.table
  after : context
  env : Env after
  correct : TablesDecision.tablesResult c items=some after

def done (c : context) (env : Env c) : Result c := ⟨[],c,env,rfl⟩
def cons (c : context) (head : Step c) (tail : Result head.after) : Result c :=
  ⟨head.item::tail.items,tail.after,tail.env,by
    simp only [TablesDecision.tablesResult,head.correct,Option.bind_some,tail.correct]⟩

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
    SpecTecExecution.Eval Body (.call ⟨context,Call.Tables_ok c out.items⟩)
      n (.success (.of out.after)) n :=
  (TablesDecision.tables_result_iff_call c out.after out.items n n env.ready env.provenance env.nested).1
    ⟨out.correct,rfl⟩

#print axioms execute
#print axioms generate_audit
end properties.wasm_module_ok.ConstructiveModuleTables
