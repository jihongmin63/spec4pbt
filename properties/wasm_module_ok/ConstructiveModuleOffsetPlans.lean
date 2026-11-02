import properties.wasm_module_ok.ConstructiveModuleInitializerPlans
import properties.wasm_module_ok.AddrNumtypeDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleOffsetPlans
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans ConstructiveConstTargetPlan ConstructiveConstTree ConstructiveConstBuilders
open ConstructiveConstTableExpand ConstructiveConstTableCoverage ConstructiveConstSeedCoverage ConstructiveConstGeneration ConstructiveConstTableSeeds

def target (c : context) (addr : addrtype) : Source c :=
  ⟨.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr),by cases addr <;> rfl⟩
def zero : addrtype → num_ | .I32AT => .I32 0 | .I64AT => .I64 0

def plan (c : context) (env : Env c) (addr : addrtype) : Productive c env :=
  ⟨target c addr,⟨0,by
    let tree : Matched c (target c addr).val := ⟨(number c (zero addr)).val,
      (number c (zero addr)).property.1,fun n => by
        cases addr <;> exact ConstNumericConsumer.match_numeric_singleton c _ n⟩
    have hc : Covers (rounds c env.ready env.provenance env.nested 0) tree.val := by
      apply covers_mono ?_ (number_cover c env.provenance (zero addr))
      intro e he
      simp only [rounds,seeds,List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl he))))
    obtain ⟨g,hg,_⟩ := operand_cover c env.ready (target c addr).val (backed c (target c addr)) _ tree hc
    exact ⟨g,hg⟩⟩⟩

def generate (c : context) (env : Env c) (addr : addrtype) :
    Audited (Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr))) :=
  expressions c env (plan c env addr)

theorem complete (c : context) (env : Env c) (addr : addrtype)
    (code : Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr))) :
    Gen.support (generate c env addr).generator code :=
  expressions_complete c env (plan c env addr) code
#print axioms complete
end properties.wasm_module_ok.ConstructiveModuleOffsetPlans
