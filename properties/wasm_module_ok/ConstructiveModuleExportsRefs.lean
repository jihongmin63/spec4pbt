import properties.wasm_module_ok.ConstructiveExports
import properties.wasm_module_ok.ConstructivePreludeRefs
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleExportsRefs
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs

theorem export_result (refs : SpecTec.free) (c : context) (used : nameset) (e : SpecTec.export) :
    ExportValidation.exportResult (replace refs c) used e=ExportValidation.exportResult c used e := by
  rw [ConstructiveExports.exportResult_shape,ConstructiveExports.exportResult_shape]
  rfl

theorem exports_result (refs : SpecTec.free) (c : context) (used : nameset) (es : List SpecTec.export) :
    ExportsValidation.exportsResult (replace refs c) used es=ExportsValidation.exportsResult c used es := by
  induction es generalizing used with
  | nil => rfl
  | cons e es ih =>
    simp only [ExportsValidation.exportsResult,export_result]
    cases he : ExportValidation.exportResult c used e with
    | none => rfl
    | some next => exact ih next

theorem exports_replace (refs : SpecTec.free) (c : context) (used out : nameset) (es : List SpecTec.export)
    (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨nameset,SpecTecCall.Exports_ok c used es⟩) n (.success (.of out)) finish) :
    Eval specTecProgram (.call ⟨nameset,SpecTecCall.Exports_ok (replace refs c) used es⟩) n (.success (.of out)) finish := by
  rw [ExportsValidation.exports_success_iff_result] at h ⊢
  exact ⟨by rw [exports_result];exact h.1,h.2⟩
#print axioms exports_replace
end properties.wasm_module_ok.ConstructiveModuleExportsRefs
