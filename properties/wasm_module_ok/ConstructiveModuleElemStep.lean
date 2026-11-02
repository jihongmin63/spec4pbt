import properties.wasm_module_ok.ConstructiveModuleElemInitializers
import properties.wasm_module_ok.ConstructiveModuleElemDataRules
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleElemStep
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans ConstructiveModuleElemInitializers

abbrev Reference (c : context) := {rt : reftype // ReftypeTotal.reftypeValid c rt=true}
theorem reference_backed (c : context) (r : Reference c) : CandidateValMatch.InTableVal c (.RefT r.val) :=
  backed c ⟨.RefT r.val,by have h:=r.property;cases he:r.val <;> simpa [he,ValtypeValidation.valtypeValid,ReftypeTotal.reftypeValid] using h⟩
def references (c : context) : Audited (Reference c) :=
  ⟨ConstructiveAttach.refine (ConstructiveTypeAtoms.reftypes c)
    (ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.reftypes_finite c)) _
    (fun r hr => (ConstructiveTypeAtoms.support_reftypes c r).1 hr),ConstructiveAttach.refine_audit _ _ _ _⟩

structure Step (c : context) where
  item : SpecTec.elem
  after : context
  env : Env after
  correct : ∀n,Eval Body (.call ⟨context,Call.Elem_ok c item⟩) n (.success (.of after)) n

def step (c : context) (env : Env c) (r : Reference c) (init : Initializers c (.RefT r.val))
    (mode : ConstructiveModuleModes.ElemMode c r.val) : Step c where
  item := ⟨r.val,init.val,mode.val⟩
  after := {c with ELEMS:=c.ELEMS++[r.val]}
  env := by
    apply ConstructiveModuleEnvironment.withElems c env
    intro rt hm
    rcases List.mem_append.mp hm with hm|hm
    · exact env.elems rt hm
    · have he : rt=r.val := by simpa using hm
      subst rt;exact reference_backed c r
  correct := fun n => ConstructiveModuleElemDataRules.elem c _ n
    ((ReftypeTotal.reftype_success_iff_valid c r.val n n).2 ⟨r.property,rfl⟩)
    (ConstructiveModuleElemInitializers.execute c r.val init n) (mode.property n)

def withInitializers (c : context) (env : Env c) (r : Reference c)
    (init : Initializers c (.RefT r.val)) : Audited (Step c) :=
  (ConstructiveModuleModes.elem c env r.val (reference_backed c r)).map (step c env r init)

def emptyBranch (c : context) (env : Env c) : Audited (Step c) :=
  (references c).bind fun r => withInitializers c env r (empty c (.RefT r.val))

def productiveReference (c : context) (env : Env c) (p : Productive c env) (rt : reftype)
    (he : p.1.val=.RefT rt) : Reference c :=
  ⟨rt,by have hv:=p.1.property;rw [he] at hv;cases rt;exact hv⟩

def castInitializers (c : context) (a b : valtype) (he : a=b) (init : Initializers c a) : Initializers c b :=
  ⟨init.val,by simpa only [he] using init.property⟩

def productiveBranch (c : context) (env : Env c) (p : Productive c env) (rt : reftype)
    (he : p.1.val=.RefT rt) : Audited (Step c) :=
  (ConstructiveModuleElemInitializers.generate c env p).bind fun init =>
    withInitializers c env (productiveReference c env p rt he) (castInitializers c _ _ he init)

def branches (c : context) (env : Env c) (round : Nat) : List (Audited (Step c)) :=
  (plans c env round).flatMap fun p =>
    match he : p.1.val with
    | .RefT rt => [productiveBranch c env p rt he]
    | _ => []

def one (c : context) (env : Env c) : Audited (Step c) :=
  (⟨Gen.arbNat,ConstructiveGenAudit.arbNat_audit⟩ : Audited Nat).bind fun round =>
    (emptyBranch c env).merge (branches c env round)

theorem complete (c out : context) (env : Env c) (item : SpecTec.elem) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Elem_ok c item⟩) n (.success (.of out)) finish) :
    ∃s : Step c,Gen.support (one c env).generator s ∧ s.item=item ∧ s.after=out := by
  obtain ⟨n1,n2,hr,hi,hm,ho⟩ := ConstructiveModuleElemDataRules.elem_original c out item n finish h
  let r : Reference c := ⟨item.ETYPE,((ReftypeTotal.reftype_success_iff_valid c item.ETYPE n n1).1 hr).1⟩
  have hall := ConstructiveModuleElemInitializers.original c env item.ETYPE (reference_backed c r) item.EINIT n1 n2 hi
  obtain ⟨mode,hmode,he⟩ := ConstructiveModuleModes.elem_complete c env item.ETYPE (reference_backed c r) item.EMODE n2 finish hm
  cases hinit : item.EINIT with
  | nil =>
    let s := step c env r (empty c (.RefT r.val)) mode
    refine ⟨s,⟨0,by simp,(merge_support _ _ _).2 ?_⟩,?_,ho.symm⟩
    · refine ⟨emptyBranch c env,List.mem_cons_self,r,?_,mode,hmode,rfl⟩
      rw [references,ConstructiveAttach.refine_support,ConstructiveTypeAtoms.support_reftypes]
      exact r.property
    · cases item;simp_all [s,step,empty,r]
  | cons code rest =>
    let target : Source c := ⟨.RefT item.ETYPE,by have h:=r.property;change ReftypeTotal.reftypeValid c item.ETYPE=true at h;cases he:item.ETYPE <;> simpa [he,ValtypeValidation.valtypeValid,ReftypeTotal.reftypeValid] using h⟩
    obtain ⟨round,⟨source,plan⟩,hp,ht⟩ := plans_complete c env target code 0 0 (hall code (by simp [hinit]) 0)
    change source=target at ht
    subst source
    let p : Productive c env := ⟨target,plan⟩
    let init : Initializers c p.1.val := ⟨item.EINIT,hall⟩
    let s := step c env r init mode
    refine ⟨s,⟨round,by simp,(merge_support _ _ _).2 ?_⟩,?_,ho.symm⟩
    · refine ⟨productiveBranch c env p item.ETYPE rfl,?_,init,ConstructiveModuleElemInitializers.complete c env p init,mode,hmode,rfl⟩
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨p,hp,by simp [p,target]⟩
    · cases item;simp_all [s,step,r,init]

#print axioms complete
end properties.wasm_module_ok.ConstructiveModuleElemStep
