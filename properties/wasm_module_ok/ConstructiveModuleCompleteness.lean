import properties.wasm_module_ok.ConstructiveModulePreludeCompleteness
import properties.wasm_module_ok.ConstructiveModuleSoundness
import properties.wasm_module_ok.ConstructiveFreeCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs

theorem matched_free (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) (p : Result)
    (hm : Matches m tr p) : ConstructiveFreeModule.moduleFree (raw p)=ConstructiveFreeModule.moduleFree m := by
  simp only [ConstructiveFreeModule.moduleFree,raw,hm.before.types,hm.before.imports,
    hm.tables,hm.memories,hm.globals,hm.elements,hm.data,hm.exports]

theorem matched_context (m : SpecTec.module) (hv : SpecTec.Module_ok m)
    (tr : Validity.ModuleOkTrace m) (p : Result) (hm : Matches m tr p) : finalContext p=tr.c8 := by
  have hf := ((ConstructiveFreeCoverage.module_free_exact m
    (ConstructiveFreeCoverage.module_ok_prelude_flat m hv) tr.free 0 tr.n1).1 tr.free_ok).1
  have h8 := (ModuleRefsValidation.module_trace_refs m tr).2.2.2.2.2.2.2.2
  have href : ConstructiveFreeModule.moduleFree m=tr.c8.REFS := hf.symm.trans h8.symm
  simp only [finalContext,hm.after,matched_free m tr p hm,href,replace]

end properties.wasm_module_ok.ConstructiveModulePrelude
namespace properties.wasm_module_ok.ConstructiveModuleFunctionList
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment

theorem complete_headers (c : context) (env : Env c) (xs : List Nat) (hr : Ready c xs)
    (fs : List SpecTec.func) (he : fs.map (·.FTYPE)=xs) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Module_ok:rule:iter:2» c fs⟩) n (.success (.of ())) finish) :
    ∃out : Result c xs,Gen.support (generate c env xs hr).generator out ∧ out.items=fs := by
  subst xs
  exact complete c env fs hr n finish h
end properties.wasm_module_ok.ConstructiveModuleFunctionList
namespace properties.wasm_module_ok.ConstructiveModuleGeneration
open SpecTec properties.wasm_module_ok SpecTecExecution

theorem modules_complete (m : SpecTec.module) (hv : SpecTec.Module_ok m) : Gen.support modules m := by
  obtain ⟨tr⟩ := Validity.module_ok_full_trace m hv
  obtain ⟨p,hp,hm⟩ := ConstructiveModulePrelude.complete m tr
  have hctx := ConstructiveModulePrelude.matched_context m hv tr p hm
  have hheader : m.FUNCS.map (·.FTYPE)=p.before.headers.items.map (·.FTYPE) := by
    rw [hm.before.headers,List.map_map]
    rfl
  have hfunc := tr.funcs_second_ok
  rw [←hctx] at hfunc
  obtain ⟨fs,hfs,hfsyn⟩ := ConstructiveModuleFunctionList.complete_headers (ConstructiveModulePrelude.finalContext p) (ConstructiveModulePrelude.finalEnv p)
    _ (ConstructiveModulePrelude.headers_ready p) m.FUNCS hheader tr.n11 tr.n12 hfunc
  have hstart := tr.start_ok
  rw [←hctx] at hstart
  obtain ⟨s,hs,hsyn⟩ := ConstructiveModuleStart.complete (ConstructiveModulePrelude.finalContext p) m.START tr.n12 tr.n13 hstart
  refine ⟨⟨p,fs,s⟩,⟨p,hp,fs,hfs,s,hs,rfl⟩,?_⟩
  change m=module ⟨p,fs,s⟩
  simp only [module,ConstructiveModulePrelude.raw,hfsyn,hsyn,hm.before.types,hm.before.imports,
    hm.tables,hm.memories,hm.globals,hm.tags,hm.elements,hm.data,hm.exports]

theorem modules_exact (m : SpecTec.module) : Gen.support modules m ↔ SpecTec.Module_ok m :=
  ⟨modules_sound m,modules_complete m⟩
#print axioms modules_complete
#print axioms modules_exact
end properties.wasm_module_ok.ConstructiveModuleGeneration
