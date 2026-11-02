import properties.wasm_module_ok.ImportsStageGenerator
import properties.wasm_module_ok.FuncHeadersStageGenerator
import properties.wasm_module_ok.MemsStageGenerator
import properties.wasm_module_ok.TagsStageGenerator
import properties.wasm_module_ok.LocalsTraversal
import properties.wasm_module_ok.StartStageGenerator
import properties.wasm_module_ok.ExportsStageGenerator

set_option autoImplicit false

namespace properties.wasm_module_ok.ModuleComponentSupport

theorem imports_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (ImportsStageGenerator.importsCorrect tr.c0).val
      m.IMPORTS := by
  have hr := (ImportsValidation.imports_success_iff_result
    tr.c0 m.IMPORTS tr.c1 tr.n3 tr.n4).1 tr.imports_ok
  rw [(ImportsStageGenerator.importsCorrect tr.c0).property]
  simp [ImportsStageGenerator.importsValid, hr.1]

theorem headers_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (FuncHeadersStageGenerator.headersCorrect tr.c1).val
      (m.FUNCS.map (·.FTYPE)) :=
  FuncHeadersStageGenerator.headersCorrect_complete
    tr.c1 m.FUNCS tr.c2 tr.n4 tr.n5 tr.funcs_ok

theorem mems_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (MemsStageGenerator.memsCorrect tr.c3).val
      m.MEMS := by
  have hr := (MemsValidation.mems_success_iff_result
    tr.c3 m.MEMS tr.c4 tr.n6 tr.n7).1 tr.mems_ok
  rw [(MemsStageGenerator.memsCorrect tr.c3).property]
  simp [MemsStageGenerator.memsValid, hr.1]

theorem tags_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (TagsStageGenerator.tagsCorrect tr.c5).val
      m.TAGS := by
  have hr := (TagsValidation.tags_success_iff_result
    tr.c5 m.TAGS tr.c6 tr.n8 tr.n9).1 tr.tags_ok
  rw [(TagsStageGenerator.tagsCorrect tr.c5).property]
  simp [TagsStageGenerator.tagsValid, hr.1]

theorem locals_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (LocalsTraversal.generate tr.c8
      (m.FUNCS.map (·.FTYPE)))
      (m.FUNCS.map (·.LOCALS)) :=
  LocalsTraversal.supported_of_validated_bodies
    tr.c8 m.FUNCS tr.n11 tr.n12 tr.funcs_second_ok

theorem start_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (StartStageGenerator.startCorrect tr.c8).val
      m.START := by
  have hr := (StartDecision.start_success_iff_valid
    tr.c8 m.START tr.n12 tr.n13).1 tr.start_ok
  rw [(StartStageGenerator.startCorrect tr.c8).property]
  exact hr.1

theorem exports_of_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    Gen.support (ExportsStageGenerator.exportCorrect tr.c8
      (SpecTec.set.«`{ % `}» ([] : List SpecTec.name))).val
      m.EXPORTS := by
  have hr := (ExportsValidation.exports_success_iff_result
    tr.c8 (SpecTec.set.«`{ % `}» ([] : List SpecTec.name))
    m.EXPORTS tr.names tr.n13 tr.n14).1 tr.exports_ok
  rw [(ExportsStageGenerator.exportCorrect tr.c8
    (SpecTec.set.«`{ % `}» ([] : List SpecTec.name))).property]
  simp [ExportsStageGenerator.valid, hr.1]

end properties.wasm_module_ok.ModuleComponentSupport
