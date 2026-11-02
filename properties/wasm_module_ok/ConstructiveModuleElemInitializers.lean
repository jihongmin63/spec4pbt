import properties.wasm_module_ok.ConstructiveModuleModes
import properties.wasm_module_ok.ConstructiveLists
import properties.wasm_module_ok.ElemInitDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleElemInitializers
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans ConstructiveConstTargetPlan ConstructiveConstTargetExact

abbrev Initializers (c : context) (t : valtype) :=
  {codes : List (List instr) // ∀code∈codes,∀n,Eval specTecProgram
    (.call ⟨Unit,SpecTecCall.Const_ok c t code⟩) n (.success (.of ())) n}
def empty (c : context) (t : valtype) : Initializers c t := ⟨[],by simp⟩

def generate (c : context) (env : Env c) (p : Productive c env) : Audited (Initializers c p.1.val) :=
  let raw := constants c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2
  let audit := constants_audit c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2
  ⟨ConstructiveAttach.refine (ConstructiveLists.all raw) (ConstructiveLists.all_audit raw audit) _
    (fun codes hc code hm n => constants_sound c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2
      code ((ConstructiveLists.all_support raw codes).1 hc code hm) n),ConstructiveAttach.refine_audit _ _ _ _⟩

theorem complete (c : context) (env : Env c) (p : Productive c env) (codes : Initializers c p.1.val) :
    Gen.support (generate c env p).generator codes := by
  rw [generate,ConstructiveAttach.refine_support,ConstructiveLists.all_support]
  intro code hm
  exact constants_complete c env.ready env.provenance env.nested p.1.val (backed c p.1) p.2 code 0 0 (codes.property code hm 0)

theorem execute (c : context) (rt : reftype) (codes : Initializers c (.RefT rt)) (n : Nat) :
    Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Elem_ok:rule:iter:0» c rt codes.val⟩) n (.success (.of ())) n := by
  rcases codes with ⟨codes,hcodes⟩
  induction codes with
  | nil => exact (ElemInitDecision.elem_iter_nil_success_iff c rt n n).2 rfl
  | cons code codes ih =>
    exact (ElemDataConstValidation.elem_iter_cons_success_iff c rt code codes n n).2
      ⟨n,hcodes code (by simp) n,ih (fun i hi => hcodes i (by simp [hi]))⟩

theorem original (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) (codes : List (List instr)) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Elem_ok:rule:iter:0» c rt codes⟩) n (.success (.of ())) finish) :
    ∀code∈codes,∀k,Eval specTecProgram (.call ⟨Unit,SpecTecCall.Const_ok c (.RefT rt) code⟩) k (.success (.of ())) k := by
  have hv := (ElemInitDecision.elem_init_valid_iff_iter c rt codes n finish env.ready env.provenance env.nested hr).2 h |>.1
  rw [ElemInitDecision.elemInitValid,List.all_eq_true] at hv
  intro code hm k
  exact (ConstExpressionDecision.constant_expression_result_iff_const_ok c _ code k env.ready env.provenance env.nested hr).1 (hv code hm)
#print axioms complete
#print axioms original
end properties.wasm_module_ok.ConstructiveModuleElemInitializers
