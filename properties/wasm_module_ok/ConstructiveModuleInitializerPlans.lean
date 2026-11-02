import properties.wasm_module_ok.ConstructiveModuleImportEnvironment
import properties.wasm_module_ok.ConstructiveConstProductivePlans
import properties.wasm_module_ok.ConstValidatedTarget
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleInitializerPlans
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTargetPlan ConstructiveConstTargetExact
open ConstructiveConstTableCore

/-- Source type metadata, constructed from literals and bounded existing type
indices. Closed DefHT values are not legal source annotations. -/
abbrev Source (c : context) := {t : valtype // ValtypeValidation.valtypeValid c t=true}

def catalog (c : context) : List (Source c) :=
  (FiniteValidTypes.validCandidates c).attach.map fun t =>
    ⟨t.val,(FiniteValidTypes.validCandidates_spec c t.val).1 t.property⟩

theorem backed (c : context) (t : Source c) : CandidateValMatch.InTableVal c t.val :=
  (ConstValidatedTarget.valid_target_in_extended_and_table c t.val t.property).2

abbrev Productive (c : context) (env : Env c) :=
  (t : Source c) × Plan c env.ready env.provenance env.nested t.val (backed c t)

/-- This table is completed before selecting any expression. A missing entry
means a target has no known constructor at this finite expansion round; it does
not discard an AST or a sampled continuation. Every listed plan is productive. -/
def plans (c : context) (env : Env c) (round : Nat) : List (Productive c env) :=
  (catalog c).flatMap fun t =>
    match planAt c env.ready env.provenance env.nested t.val (backed c t) round with
    | none => []
    | some plan => [⟨t,plan⟩]

abbrev Constant (c : context) (target : valtype) :=
  {code : List instr // ∀n,SpecTecExecution.Eval specTecProgram
    (.call ⟨Unit,SpecTecCall.Const_ok c target code⟩) n (.success (.of ())) n}

def expressions (c : context) (env : Env c) (p : Productive c env) : Audited (Constant c p.1.val) :=
  ⟨ConstructiveAttach.refine
    (constants c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2)
    (constants_audit c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2) _
    (fun code hc n => constants_sound c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2 code hc n),
    ConstructiveAttach.refine_audit _ _ _ _⟩

theorem catalog_mem (c : context) (t : Source c) : t∈catalog c := by
  refine List.mem_map.mpr ⟨⟨t.val,(FiniteValidTypes.validCandidates_spec c t.val).2 t.property⟩,by simp,?_⟩
  exact Subtype.ext rfl

theorem plans_complete (c : context) (env : Env c) (target : Source c) (code : List instr)
    (start finish : Nat) (h : SpecTecExecution.Eval specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target.val code⟩) start (.success (.of ())) finish) :
    ∃round,∃p : Productive c env,p∈plans c env round ∧ p.1=target := by
  obtain ⟨round,plan,hp⟩ := original_has_plan c env.ready env.provenance env.nested
    target.val (backed c target) code start finish h
  exact ⟨round,⟨target,plan⟩,List.mem_flatMap.mpr ⟨target,catalog_mem c target,by simp [hp]⟩,rfl⟩

theorem expressions_complete (c : context) (env : Env c) (p : Productive c env)
    (code : Constant c p.1.val) : Gen.support (expressions c env p).generator code := by
  rw [expressions,ConstructiveAttach.refine_support]
  exact constants_complete c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2
    code.val 0 0 (code.property 0)

#print axioms plans_complete
#print axioms expressions_complete
end properties.wasm_module_ok.ConstructiveModuleInitializerPlans
