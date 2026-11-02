import properties.wasm_module_ok.ModuleComponentSupport

set_option autoImplicit false

namespace properties.wasm_module_ok.StateStageTrace

theorem imports_state_iff_call
    (c out : SpecTec.context)
    (is : List SpecTec.«import») (n : Nat) :
    Gen.support (ImportsStageGenerator.importsStateGen c) (is, out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Imports_ok c is⟩)
        n (.success (.of out)) n := by
  rw [ImportsStageGenerator.importsState_support_iff,
    ImportsValidation.imports_success_iff_result]
  simp

theorem headers_state_iff_call
    (c out : SpecTec.context)
    (fs : List SpecTec.func) (n : Nat) :
    Gen.support (FuncHeadersStageGenerator.headersStateGen c)
      (fs.map (·.FTYPE), out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Funcs_ok c fs⟩)
        n (.success (.of out)) n := by
  rw [FuncHeadersStageGenerator.headersState_support_iff,
    FuncHeadersStageGenerator.funcs_success_iff_header_result]
  simp

theorem mems_state_iff_call
    (c out : SpecTec.context)
    (ms : List SpecTec.memory) (n : Nat) :
    Gen.support (MemsStageGenerator.memsStateGen c) (ms, out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Mems_ok c ms⟩)
        n (.success (.of out)) n := by
  rw [MemsStageGenerator.memsState_support_iff,
    MemsValidation.mems_success_iff_result]
  simp

theorem tags_state_iff_call
    (c out : SpecTec.context)
    (ts : List SpecTec.tag) (n : Nat) :
    Gen.support (TagsStageGenerator.tagsStateGen c) (ts, out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Tags_ok c ts⟩)
        n (.success (.of out)) n := by
  rw [TagsStageGenerator.tagsState_support_iff,
    TagsValidation.tags_success_iff_result]
  simp

theorem start_state_iff_call
    (c : SpecTec.context)
    (s : Option SpecTec.start) (n : Nat) :
    Gen.support (StartStageGenerator.startStateGen c) (s, c) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c s⟩)
        n (.success (.of ())) n := by
  rw [StartStageGenerator.startState_support_iff,
    StartDecision.start_success_iff_valid]
  simp

theorem exports_state_iff_call
    (c : SpecTec.context) (names out : SpecTec.nameset)
    (es : List SpecTec.«export») (n : Nat) :
    Gen.support (ExportsStageGenerator.exportsStateGen c names)
      (es, out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.nameset,
          SpecTec.SpecTecCall.Exports_ok c names es⟩)
        n (.success (.of out)) n := by
  rw [ExportsStageGenerator.exportsState_support_iff,
    ExportsValidation.exports_success_iff_result]
  simp

end properties.wasm_module_ok.StateStageTrace
