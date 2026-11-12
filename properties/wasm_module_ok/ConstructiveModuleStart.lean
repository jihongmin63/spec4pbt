import properties.wasm_module_ok.ConstructiveBodyLookup
import properties.wasm_module_ok.StartDecision
import properties.wasm_module_ok.ConstructiveConstTableCore
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleStart
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveConstTableCore

abbrev Result (c : context) := {s : Option SpecTec.start // ∀n,Eval Body
  (.call ⟨Unit,Call.Start_ok c s⟩) n (.success (.of ())) n}
def none (c : context) : Result c := ⟨Option.none,StartValidation.start_none_success c⟩
def some (c : context) (e : ConstructiveBodyLookup.Entry c.FUNCS)
    (he : UnrollInterface.deftypeFunctype e.value=Option.some (.FuncT [] [])) : Result c :=
  ⟨Option.some ⟨e.index⟩,fun n => (StartDecision.start_some_success_iff_result c _ n n).2
    ⟨⟨e.value,e.lookup,he⟩,rfl⟩⟩

def choices (c : context) : List (Result c) :=
  (ConstructiveBodyLookup.entries c.FUNCS).flatMap fun e =>
    if he : UnrollInterface.deftypeFunctype e.value=Option.some (.FuncT [] []) then [some c e he] else []
def generate (c : context) : Gen (Result c) := ConstructiveTypeAtoms.choose (none c) (choices c)
theorem generate_audit (c : context) : ConstructiveGenAudit.Structural (generate c) :=
  ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.finite_choose _ _)

theorem complete (c : context) (s : Option SpecTec.start) (n finish : Nat)
    (h : Eval Body (.call ⟨Unit,Call.Start_ok c s⟩) n (.success (.of ())) finish) :
    ∃out : Result c,Gen.support (generate c) out ∧ out.val=s := by
  cases s with
  | none => exact ⟨none c,(ConstructiveTypeAtoms.support_choose _ _ _).2 List.mem_cons_self,rfl⟩
  | some s =>
    obtain ⟨⟨dt,hx,hf⟩,_⟩ := (StartDecision.start_some_success_iff_result c s n finish).1 h
    let e : ConstructiveBodyLookup.Entry c.FUNCS := ⟨s.SFUNC,dt,hx⟩
    refine ⟨some c e hf,(ConstructiveTypeAtoms.support_choose _ _ _).2 ?_,by cases s;rfl⟩
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨e,ConstructiveBodyLookup.complete _ e,by simp [e,hf]⟩
#print axioms complete
end properties.wasm_module_ok.ConstructiveModuleStart
