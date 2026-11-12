import properties.wasm_module_ok.DeclarationTypesValidation
import properties.wasm_module_ok.ContextTypesValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.LateTypesTransport

theorem trace_header_types (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    tr.c8.TYPES = tr.c1.TYPES := by
  have hheaders :=
    (FuncHeadersStageGenerator.funcs_success_iff_header_result
      tr.c1 m.FUNCS tr.c2 tr.n4 tr.n5).1 tr.funcs_ok
  have hmems :=
    (MemsValidation.mems_success_iff_result
      tr.c3 m.MEMS tr.c4 tr.n6 tr.n7).1 tr.mems_ok
  have htags :=
    (TagsValidation.tags_success_iff_result
      tr.c5 m.TAGS tr.c6 tr.n8 tr.n9).1 tr.tags_ok
  calc
    tr.c8.TYPES = tr.c7.TYPES :=
      DeclarationTypesValidation.datas_ok_types
        tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok
    _ = tr.c6.TYPES :=
      DeclarationTypesValidation.elems_ok_types
        tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok
    _ = tr.c5.TYPES :=
      ContextTypesValidation.tags_types tr.c5 tr.c6 m.TAGS htags.1
    _ = tr.c4.TYPES :=
      DeclarationTypesValidation.globals_ok_types
        tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8 tr.globals_ok
    _ = tr.c3.TYPES :=
      ContextTypesValidation.mems_types tr.c3 tr.c4 m.MEMS hmems.1
    _ = tr.c2.TYPES :=
      DeclarationTypesValidation.tables_ok_types
        tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok
    _ = tr.c1.TYPES :=
      ContextTypesValidation.headers_types tr.c1 tr.c2
        (m.FUNCS.map (·.FTYPE)) hheaders.1

theorem completed_bodies_for_trace (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Module_ok:rule:iter:2»
        tr.c8 ((m.FUNCS.map (·.FTYPE)).map
          HeaderBodyCompletion.completedFunction)⟩)
      tr.n11 (.success (.of ())) tr.n11 := by
  have hheaders :=
    (FuncHeadersStageGenerator.funcs_success_iff_header_result
      tr.c1 m.FUNCS tr.c2 tr.n4 tr.n5).1 tr.funcs_ok
  exact HeaderBodyCompletion.completed_bodies_total_of_same_types
    tr.c1 tr.c8 tr.c2 (m.FUNCS.map (·.FTYPE)) tr.n11
    hheaders.1 (trace_header_types m tr).symm

end properties.wasm_module_ok.LateTypesTransport
