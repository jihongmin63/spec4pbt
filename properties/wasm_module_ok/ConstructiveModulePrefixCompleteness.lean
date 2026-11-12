import properties.wasm_module_ok.ConstructiveModulePrelude
import properties.wasm_module_ok.Validity
import properties.wasm_module_ok.ConstructivePreludeRefs
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs
open properties.wasm_module_not_ok.Rejection

structure PrefixMatches (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) (p : Prefix) : Prop where
  types : p.types.types=m.TYPES
  imports : p.imports.items=m.IMPORTS
  headers : p.headers.items=(m.FUNCS.map (fun f => ConstructiveModuleHeaders.header f.FTYPE))
  c0 : p.types.after=replace emptyFree tr.c0
  c1 : p.imports.after=replace emptyFree tr.c1
  c2 : p.headers.after=replace emptyFree tr.c2

theorem prefix_complete (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    ∃p : Prefix,Gen.support prefixGen p ∧ PrefixMatches m tr p := by
  have hc : tr.c=emptyContext := by
    obtain ⟨he,_⟩ := properties.wasm_module_ok.Execution.eval_deterministic tr.empty_ok
      (empty_context_total tr.n1)
    exact eq_of_heq (Value.of.inj (Outcome.success.inj he)).2
  have htypes := tr.types_ok
  rw [hc] at htypes
  have hts : Eval Body (.call ⟨context,Call.Types_ok initial m.TYPES⟩)
      tr.n2 (.success (.of (replace emptyFree tr.c0))) tr.n3 :=
    ConstructivePreludeRefs.types_replace emptyFree {emptyContext with REFS:=tr.free} _ _ tr.n2 tr.n3 (.seed _ rfl) htypes
  obtain ⟨ts,hts,hsyn,htout⟩ := ConstructiveTypes.generate_complete initial (replace emptyFree tr.c0)
    (ConstructiveTypesState.empty initial rfl) m.TYPES tr.n2 tr.n3 hts
  have his := ConstructivePreludeRefs.imports_replace emptyFree _ _ _ tr.n3 tr.n4 tr.imports_ok
  rw [←htout] at his
  obtain ⟨is,his,hisyn,hiout⟩ := ConstructiveImports.generate_complete ts.after (replace emptyFree tr.c1) m.IMPORTS
    ((ImportsValidation.imports_success_iff_result _ _ _ tr.n3 tr.n4).1 his).1
  have hfs := ConstructivePreludeRefs.funcs_replace emptyFree _ _ _ tr.n4 tr.n5 tr.funcs_ok
  rw [←hiout] at hfs
  have hfr := (FuncsValidation.funcs_success_iff_result _ _ _ tr.n4 tr.n5).1 hfs |>.1
  have hcanon : FuncsValidation.funcsResult is.after ((m.FUNCS.map (·.FTYPE)).map ConstructiveModuleHeaders.header)=
      some (replace emptyFree tr.c2) := by
    rw [FuncHeadersStageGenerator.funcs_header_invariant] at hfr
    exact hfr
  let ei := ConstructiveModuleImportEnvironment.generated ts.after (ConstructiveModuleTypesEnvironment.generated _ ts) is
  obtain ⟨fs,hfs,hfsyn,hfout⟩ := ConstructiveModuleHeaders.generate_complete is.after (replace emptyFree tr.c2) ei
    (m.FUNCS.map (·.FTYPE)) hcanon
  refine ⟨⟨ts,is,fs⟩,⟨ts,hts,is,his,fs,hfs,rfl⟩,hsyn,hisyn,?_,htout,hiout,hfout⟩
  exact hfsyn.trans (by rw [List.map_map]; rfl)
#print axioms prefix_complete
end properties.wasm_module_ok.ConstructiveModulePrelude
