import properties.wasm_module_ok.ConstructiveModulePrelude
import properties.wasm_module_ok.ConstructiveModuleFunctionList
import properties.wasm_module_ok.ContextTypesValidation
import properties.wasm_module_ok.DeclarationTypesValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok

theorem final_types (p : Result) : (finalContext p).TYPES=p.before.imports.after.TYPES := by
  have h0 : p.before.headers.after.TYPES=p.before.imports.after.TYPES := by
    apply ContextTypesValidation.headers_types _ _ (p.before.headers.items.map (·.FTYPE))
    rw [←FuncHeadersStageGenerator.funcs_header_invariant]
    exact p.before.headers.correct
  have h1 := DeclarationTypesValidation.tables_ok_types _ _ _ 0 0
    (ConstructiveModuleTables.execute _ (boundedEnv p.before) p.tables 0)
  have h2 := ContextTypesValidation.mems_types _ _ _ p.memories.correct
  have h3 := DeclarationTypesValidation.globals_ok_types _ _ _ 0 0
    (ConstructiveModuleGlobals.execute _ p.memories.env p.globals 0)
  have h4 := ContextTypesValidation.tags_types _ _ _ p.tags.correct
  have h5 := DeclarationTypesValidation.elems_ok_types _ _ _ 0 0 (p.elements.correct 0)
  have h6 := DeclarationTypesValidation.datas_ok_types _ _ _ 0 0 (p.data.correct 0)
  exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans (h1.trans h0)))))

theorem headers_ready (p : Result) :
    ConstructiveModuleFunctionList.Ready (finalContext p) (p.before.headers.items.map (·.FTYPE)) := by
  intro x hx
  have hh : FuncHeadersStageGenerator.headerResult p.before.imports.after
      (p.before.headers.items.map (·.FTYPE))=some p.before.headers.after := by
    rw [←FuncHeadersStageGenerator.funcs_header_invariant]
    exact p.before.headers.correct
  obtain ⟨ft,hf⟩ := HeaderBodyCompletion.header_member_has_type _ _ _ hh x hx
  have he := HeaderBodyCompletion.func_type_result_eq_of_types p.before.imports.after (finalContext p) x
    (final_types p).symm
  rw [←he,hf]
  rfl
#print axioms headers_ready
end properties.wasm_module_ok.ConstructiveModulePrelude
