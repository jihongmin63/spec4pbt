import properties.wasm_module_ok.ConstructiveModuleInitializerRefs
import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.ModuleRefsValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleTraceFields
open SpecTec properties.wasm_module_ok SpecTecExecution

theorem globals_funcs (c out : context) (xs : List SpecTec.global) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Globals_ok c xs⟩) n (.success (.of out)) finish) : out.FUNCS=c.FUNCS := by
  induction xs generalizing c n with
  | nil => exact congrArg context.FUNCS ((GlobalsDecision.globals_nil_success_iff c out n finish).1 h).1.symm
  | cons g gs ih =>
    obtain ⟨next,middle,hh,ht⟩ := (GlobalsDecision.globals_cons_success_iff c out g gs n finish).1 h
    exact (ih next middle ht).trans (ConstructiveModuleInitializerRefs.global_ok_funcs c next g n middle hh)

theorem funcs (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    tr.c3.FUNCS=tr.c2.FUNCS ∧ tr.c4.FUNCS=tr.c2.FUNCS ∧ tr.c5.FUNCS=tr.c2.FUNCS ∧
    tr.c6.FUNCS=tr.c2.FUNCS ∧ tr.c7.FUNCS=tr.c2.FUNCS ∧ tr.c8.FUNCS=tr.c2.FUNCS := by
  have h3 := CandidateProvenancePreGlobals.tables_ok_funcs _ _ _ _ _ tr.tables_ok
  have h4 := (CandidateProvenancePreGlobals.mems_result_funcs _ _ _
    ((MemsValidation.mems_success_iff_result _ _ _ _ _).1 tr.mems_ok).1).trans h3
  have h5 := (globals_funcs _ _ _ _ _ tr.globals_ok).trans h4
  have h6 := (CandidateProvenancePostGlobals.tags_result_funcs _ _ _
    ((TagsValidation.tags_success_iff_result _ _ _ _ _).1 tr.tags_ok).1).trans h5
  have h7 := (CandidateProvenanceElemDataFuncs.elems_ok_funcs _ _ _ _ _ tr.elems_ok).trans h6
  have h8 := (CandidateProvenanceElemDataFuncs.datas_ok_funcs _ _ _ _ _ tr.datas_ok).trans h7
  exact ⟨h3,h4,h5,h6,h7,h8⟩

theorem allFunctions_eq (c d : context) (h : c.FUNCS=d.FUNCS) :
    ConstructiveModuleRefsBounds.allFunctions c=ConstructiveModuleRefsBounds.allFunctions d := by
  simp only [ConstructiveModuleRefsBounds.allFunctions,h]
#print axioms funcs
end properties.wasm_module_ok.ConstructiveModuleTraceFields
