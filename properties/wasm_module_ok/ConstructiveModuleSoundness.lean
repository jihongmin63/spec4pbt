import properties.wasm_module_ok.ConstructiveModuleGeneration
import properties.wasm_module_ok.ConstructiveModulePreludeFree
import properties.wasm_module_ok.ConstructiveModuleInitializerRefs
import properties.wasm_module_ok.ConstructiveModuleElemDataListRefs
import properties.wasm_module_ok.ConstructiveModuleExportsRefs
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleGeneration
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs

/-- Assemble a new original ModuleOkTrace from actual generated local witnesses.
No validity of the new module is assumed, and its exact syntax determines REFS. -/
theorem original (out : Result) : SpecTec.Module_ok (module out) := by
  let p := out.prelude
  let refs := ConstructiveFreeModule.moduleFree (ConstructiveModulePrelude.raw p)
  obtain ⟨names,hex⟩ := (ConstructiveExports.exports_exact p.data.after (.«`{ % `}» []) p.exports.val 0).1 p.exports.property
  have hf : Eval Body (.call ⟨context,Call.Funcs_ok p.before.imports.after out.functions.items⟩)
      0 (.success (.of p.before.headers.after)) 0 := by
    apply (FuncsValidation.funcs_success_iff_result _ _ _ 0 0).2
    refine ⟨?_,rfl⟩
    rw [FuncHeadersStageGenerator.funcs_header_invariant,out.functions.headers,
      ←FuncHeadersStageGenerator.funcs_header_invariant]
    exact p.before.headers.correct
  have ht := ConstructiveModuleInitializerRefs.tables_replace refs _ _ p.tables.items 0 0
    (fun t ht => ConstructiveModulePrelude.initializer_available p t.TINIT (.table t ht))
    (ConstructiveModuleTables.execute _ (ConstructiveModulePrelude.boundedEnv p.before) p.tables 0)
  have hg := ConstructiveModuleInitializerRefs.globals_replace refs _ _ p.globals.items 0 0
    (fun g hg => ConstructiveModulePrelude.initializer_available p g.GINIT (.global g hg))
    (ConstructiveModuleGlobals.execute _ p.memories.env p.globals 0)
  have he := ConstructiveModuleElemDataRefs.elems_replace refs _ _ p.elements.items 0 0 (by
    intro e he
    constructor
    · intro xs hx;exact ConstructiveModulePrelude.initializer_available p xs (.elemInit e xs he hx)
    · cases hm : e.EMODE with
      | Passive => trivial
      | Declarative => trivial
      | Active a => exact ConstructiveModulePrelude.initializer_available p a.OFFSET (.elemOffset e a he hm))
    (p.elements.correct 0)
  have hd := ConstructiveModuleElemDataRefs.datas_replace refs _ _ p.data.items 0 0 (by
    intro d hd
    change ConstructiveModuleModeRefs.DataAvailable refs d.DMODE
    cases hm : d.DMODE with
    | Passive => trivial
    | Active a => exact ConstructiveModulePrelude.initializer_available p a.OFFSET (.dataOffset d a hd hm))
    (p.data.correct 0)
  apply Validity.module_ok_of_full_trace
  exact ⟨{
    free := refs
    c := properties.wasm_module_not_ok.Rejection.emptyContext
    c0 := replace refs p.before.types.after
    c1 := replace refs p.before.imports.after
    c2 := replace refs p.before.headers.after
    c3 := replace refs p.tables.after
    c4 := replace refs p.memories.after
    c5 := replace refs p.globals.after
    c6 := replace refs p.tags.after
    c7 := replace refs p.elements.after
    c8 := replace refs p.data.after
    names := names
    n1 := 0, n2 := 0, n3 := 0, n4 := 0, n5 := 0, n6 := 0, n7 := 0
    n8 := 0, n9 := 0, n10 := 0, n11 := 0, n12 := 0, n13 := 0, n14 := 0
    free_ok := ConstructiveFreeModule.module_free_total (ConstructiveModulePrelude.raw p) 0 (ConstructiveModulePrelude.prelude_flat p)
    empty_ok := properties.wasm_module_not_ok.Rejection.empty_context_total 0
    types_ok := ConstructivePreludeRefs.types_replace refs _ _ _ 0 0 (.seed _ rfl) (p.before.types.correct 0)
    imports_ok := ConstructivePreludeRefs.imports_replace refs _ _ _ 0 0 (ConstructiveImports.execute _ p.before.imports 0)
    funcs_ok := ConstructivePreludeRefs.funcs_replace refs _ _ _ 0 0 hf
    tables_ok := ht
    mems_ok := ConstructivePreludeRefs.mems_replace refs _ _ _ 0 0 (ConstructiveModuleMemories.execute _ p.memories 0)
    globals_ok := hg
    tags_ok := ConstructivePreludeRefs.tags_replace refs _ _ _ 0 0 (ConstructiveModuleTags.execute _ p.tags 0)
    elems_ok := he
    datas_ok := hd
    funcs_second_ok := out.functions.correct 0
    start_ok := out.start.property 0
    exports_ok := ConstructiveModuleExportsRefs.exports_replace refs _ _ names _ 0 0 hex
  }⟩

theorem modules_sound (m : SpecTec.module) (h : Gen.support modules m) : SpecTec.Module_ok m := by
  obtain ⟨out,_,he⟩ := h
  rw [he]
  exact original out
#print axioms original
#print axioms modules_sound
end properties.wasm_module_ok.ConstructiveModuleGeneration
