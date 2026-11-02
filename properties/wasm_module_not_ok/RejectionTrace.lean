import properties.wasm_module_not_ok.Rejection

set_option autoImplicit false

namespace properties.wasm_module_not_ok.RejectionTrace

open properties.wasm_module_not_ok.Rejection

/-- The successful calls made by the generated `Module_ok` clause, in order. -/
structure ModuleValidationTrace (m : SpecTec.module) : Type where
  free : SpecTec.free
  c : SpecTec.context
  c0 : SpecTec.context
  c1 : SpecTec.context
  c2 : SpecTec.context
  c3 : SpecTec.context
  c4 : SpecTec.context
  c5 : SpecTec.context
  c6 : SpecTec.context
  c7 : SpecTec.context
  c8 : SpecTec.context
  names : SpecTec.nameset
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n4 : Nat
  n5 : Nat
  n6 : Nat
  n7 : Nat
  n8 : Nat
  n9 : Nat
  n10 : Nat
  n11 : Nat
  n12 : Nat
  n13 : Nat
  n14 : Nat
  free_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module»
      ({ {m with FUNCS := []} with START := none })⟩)
    0 (.success (.of free)) n1
  empty_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.«$empty_context»⟩)
    n1 (.success (.of c)) n2
  types_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok
      {c with REFS := free} m.TYPES⟩)
    n2 (.success (.of c0)) n3
  imports_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Imports_ok c0 m.IMPORTS⟩)
    n3 (.success (.of c1)) n4
  funcs_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Funcs_ok c1 m.FUNCS⟩)
    n4 (.success (.of c2)) n5
  tables_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Tables_ok c2 m.TABLES⟩)
    n5 (.success (.of c3)) n6
  mems_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mems_ok c3 m.MEMS⟩)
    n6 (.success (.of c4)) n7
  globals_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Globals_ok c4 m.GLOBALS⟩)
    n7 (.success (.of c5)) n8
  tags_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Tags_ok c5 m.TAGS⟩)
    n8 (.success (.of c6)) n9
  elems_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elems_ok c6 m.ELEMS⟩)
    n9 (.success (.of c7)) n10
  datas_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Datas_ok c7 m.DATAS⟩)
    n10 (.success (.of c8)) n11
  funcs_second_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨Unit, SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c8 m.FUNCS⟩)
    n11 (.success (.of ())) n12
  start_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c8 m.START⟩)
    n12 (.success (.of ())) n13
  exports_ok : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.nameset, SpecTec.SpecTecCall.Exports_ok c8
      (SpecTec.set.«`{ % `}» ([] : List SpecTec.name)) m.EXPORTS⟩)
    n13 (.success (.of names)) n14

theorem module_ok_full_validation_trace (m : SpecTec.module) :
    SpecTec.Module_ok m → Nonempty (ModuleValidationTrace m) := by
  intro h
  obtain ⟨_, hclause⟩ := (module_clause_success_iff m).mp h
  cases hclause with
  | bind_success hfree htail =>
    cases htail with
    | bind_success hempty htail =>
      cases htail with
      | bind_success htypes htail =>
        cases htail with
        | bind_success himports htail =>
          cases htail with
          | bind_success hfuncs htail =>
            cases htail with
            | bind_success htables htail =>
              cases htail with
              | bind_success hmems htail =>
                cases htail with
                | bind_success hglobals htail =>
                  cases htail with
                  | bind_success htags htail =>
                    cases htail with
                    | bind_success helems htail =>
                      cases htail with
                      | bind_success hdatas htail =>
                        cases htail with
                        | bind_success hfuncs2 htail =>
                          cases htail with
                          | bind_success hstart htail =>
                            cases htail with
                            | bind_success hexports _ =>
                              refine ⟨{
                                free := _,
                                c := _, c0 := _, c1 := _, c2 := _, c3 := _,
                                c4 := _, c5 := _, c6 := _, c7 := _, c8 := _,
                                names := _,
                                n1 := _, n2 := _, n3 := _, n4 := _, n5 := _,
                                n6 := _, n7 := _, n8 := _, n9 := _, n10 := _,
                                n11 := _, n12 := _, n13 := _, n14 := _,
                                free_ok := hfree, empty_ok := hempty,
                                types_ok := htypes, imports_ok := himports,
                                funcs_ok := hfuncs, tables_ok := htables,
                                mems_ok := hmems, globals_ok := hglobals,
                                tags_ok := htags, elems_ok := helems,
                                datas_ok := hdatas, funcs_second_ok := hfuncs2,
                                start_ok := hstart, exports_ok := hexports
                              }⟩

theorem module_ok_of_full_validation_trace (m : SpecTec.module) :
    Nonempty (ModuleValidationTrace m) → SpecTec.Module_ok m := by
  rintro ⟨trace⟩
  apply (module_clause_success_iff m).2
  refine ⟨trace.n14, ?_⟩
  apply SpecTecExecution.Eval.bind_success trace.free_ok
  apply SpecTecExecution.Eval.bind_success trace.empty_ok
  apply SpecTecExecution.Eval.bind_success trace.types_ok
  apply SpecTecExecution.Eval.bind_success trace.imports_ok
  apply SpecTecExecution.Eval.bind_success trace.funcs_ok
  apply SpecTecExecution.Eval.bind_success trace.tables_ok
  apply SpecTecExecution.Eval.bind_success trace.mems_ok
  apply SpecTecExecution.Eval.bind_success trace.globals_ok
  apply SpecTecExecution.Eval.bind_success trace.tags_ok
  apply SpecTecExecution.Eval.bind_success trace.elems_ok
  apply SpecTecExecution.Eval.bind_success trace.datas_ok
  apply SpecTecExecution.Eval.bind_success trace.funcs_second_ok
  apply SpecTecExecution.Eval.bind_success trace.start_ok
  apply SpecTecExecution.Eval.bind_success trace.exports_ok
  exact .pure ()


theorem module_ok_iff_validation_trace (m : SpecTec.module) :
    SpecTec.Module_ok m ↔ Nonempty (ModuleValidationTrace m) := by
  exact ⟨module_ok_full_validation_trace m, module_ok_of_full_validation_trace m⟩

theorem not_module_ok_iff_no_validation_trace (m : SpecTec.module) :
    ¬ SpecTec.Module_ok m ↔ ¬ Nonempty (ModuleValidationTrace m) := by
  rw [module_ok_iff_validation_trace]

end properties.wasm_module_not_ok.RejectionTrace
