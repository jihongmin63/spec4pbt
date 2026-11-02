import properties.wasm_module_ok.ConstructiveModuleEnvironment
import properties.wasm_module_ok.ConstructiveImportEntries
import properties.wasm_module_ok.MemsValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleMemories
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore

abbrev Memory := {mt : memtype // MemtypeValidation.memtypeValid mt=true}
def memories : Audited Memory :=
  ⟨ConstructiveAttach.refine ConstructiveLimits.memories
    (ConstructiveGenAudit.finite_audit _ ConstructiveLimits.memories_finite) _
    (fun mt hm => (ConstructiveLimits.memories_support mt).1 hm),ConstructiveAttach.refine_audit _ _ _ _⟩
structure Result (c : context) where
  items : List memory
  after : context
  env : Env after
  correct : MemsValidation.memsResult c items=some after

def done (c : context) (env : Env c) : Result c := ⟨[],c,env,rfl⟩
def next (c : context) (mt : Memory) : context := {c with MEMS:=c.MEMS++[mt.val]}
def nextEnv (c : context) (env : Env c) (mt : Memory) : Env (next c mt) :=
  ConstructiveModuleEnvironment.withMems c env _
def cons (c : context) (mt : Memory) (tail : Result (next c mt)) : Result c :=
  ⟨⟨mt.val⟩::tail.items,tail.after,tail.env,by
    simpa [MemsValidation.memsResult,MemsValidation.memDeclResult,mt.property,next] using tail.correct⟩

def sized : Nat → (c : context) → Env c → Audited (Result c)
  | 0,c,env => Audited.pure (done c env)
  | n+1,c,env => memories.bind fun mt =>
      (sized n (next c mt) (nextEnv c env mt)).map (cons c mt)
def generate (c : context) (env : Env c) : Gen (Result c) :=
  Gen.arbNat >>= fun n => (sized n c env).generator

theorem generate_audit (c : context) (env : Env c) : ConstructiveGenAudit.Structural (generate c env) :=
  ⟨ConstructiveGenAudit.arbNat_audit,fun n => (sized n c env).audit⟩
theorem execute (c : context) (out : Result c) (n : Nat) :
    SpecTecExecution.Eval specTecProgram (.call ⟨context,SpecTecCall.Mems_ok c out.items⟩)
      n (.success (.of out.after)) n :=
  (MemsValidation.mems_success_iff_result c out.items out.after n n).2 ⟨out.correct,rfl⟩

theorem sized_complete (c result : context) (env : Env c) (xs : List memory)
    (h : MemsValidation.memsResult c xs=some result) :
    ∃out : Result c,Gen.support (sized xs.length c env).generator out ∧ out.items=xs ∧ out.after=result := by
  induction xs generalizing c with
  | nil => exact ⟨done c env,rfl,rfl,Option.some.inj h⟩
  | cons x xs ih =>
    cases hv : MemtypeValidation.memtypeValid x.MTYPE with
    | false => simp [MemsValidation.memsResult,MemsValidation.memDeclResult,hv] at h
    | true =>
      let mt : Memory := ⟨x.MTYPE,hv⟩
      have ht : MemsValidation.memsResult (next c mt) xs=some result := by
        simpa only [MemsValidation.memsResult,MemsValidation.memDeclResult,hv,ite_true,Option.bind_some,next,mt] using h
      obtain ⟨tail,hg,hs,ho⟩ := ih (next c mt) (nextEnv c env mt) ht
      have hm : Gen.support memories.generator mt := by
        rw [memories,ConstructiveAttach.refine_support,ConstructiveLimits.memories_support];exact hv
      refine ⟨cons c mt tail,⟨mt,hm,tail,hg,rfl⟩,?_,ho⟩
      cases x; simp [cons,mt,hs]

theorem generate_complete (c result : context) (env : Env c) (xs : List memory)
    (start finish : Nat) (h : SpecTecExecution.Eval specTecProgram
      (.call ⟨context,SpecTecCall.Mems_ok c xs⟩) start (.success (.of result)) finish) :
    ∃out : Result c,Gen.support (generate c env) out ∧ out.items=xs ∧ out.after=result := by
  obtain ⟨out,hg,hs,ho⟩ := sized_complete c result env xs
    ((MemsValidation.mems_success_iff_result c xs result start finish).1 h).1
  exact ⟨out,⟨xs.length,by simp,hg⟩,hs,ho⟩
#print axioms generate_complete
end properties.wasm_module_ok.ConstructiveModuleMemories
