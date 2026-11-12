import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.Validity

private theorem singleton_clause_success_inv
    {clause : SpecTecExecution.Action.{1} SpecTec.Request}
    {start finalSupply : Nat} {value : SpecTecExecution.Value}
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses [clause]) start
      (.success value) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      clause start (.success value) finalSupply := by
  change SpecTecExecution.Eval SpecTec.Body
    (.orElse clause (fun _ => .unmatch)) start
    (.success value) finalSupply at h
  cases h with
  | orElse_success hc => exact hc
  | orElse_unmatch hfailedSupply htail => restore_supply hfailedSupply at htail; cases htail

theorem module_ok_clause_success (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ finalSupply : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Module_ok:clause:0» m) 0
          (.success (.of ())) finalSupply := by
  intro h
  change ∃ finalSupply : Nat,
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
      (.success (.of ())) finalSupply at h
  obtain ⟨finalSupply, heval⟩ := h
  cases heval with
  | call hbody =>
      refine ⟨finalSupply, ?_⟩
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Module_ok_clauses m)) 0
        (.success (.of ())) finalSupply at hbody
      simpa only [SpecTec.Module_ok_clauses] using
        (singleton_clause_success_inv hbody)

theorem module_ok_free_module_success (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ (free : SpecTec.free) (middle : Nat),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
            ({ {m with FUNCS := []} with START := none })⟩)
          0 (.success (.of free)) middle := by
  intro h
  obtain ⟨finalSupply, hclause⟩ := module_ok_clause_success m h
  cases hclause with
  | bind_success hfree _ =>
      exact ⟨_, _, hfree⟩

theorem module_ok_initial_context (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ (free : SpecTec.free) (c : SpecTec.context)
        (n₁ n₂ : Nat),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
            ({ {m with FUNCS := []} with START := none })⟩)
          0 (.success (.of free)) n₁ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
          n₁ (.success (.of c)) n₂ := by
  intro h
  obtain ⟨finalSupply, hclause⟩ := module_ok_clause_success m h
  cases hclause with
  | bind_success hfree htail =>
      cases htail with
      | bind_success hcontext _ =>
          exact ⟨_, _, _, _, hfree, hcontext⟩

theorem module_ok_types_success (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ (free : SpecTec.free) (c c₀ : SpecTec.context)
        (n₁ n₂ n₃ : Nat),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
            ({ {m with FUNCS := []} with START := none })⟩)
          0 (.success (.of free)) n₁ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
          n₁ (.success (.of c)) n₂ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
          n₂ (.success (.of c₀)) n₃ := by
  intro h
  obtain ⟨finalSupply, hclause⟩ := module_ok_clause_success m h
  cases hclause with
  | bind_success hfree htail =>
      cases htail with
      | bind_success hcontext htail =>
          cases htail with
          | bind_success htypes _ =>
              exact ⟨_, _, _, _, _, _, hfree, hcontext, htypes⟩

theorem module_ok_imports_success (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ (free : SpecTec.free) (c c₀ c₁ : SpecTec.context)
        (n₁ n₂ n₃ n₄ : Nat),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
            ({ {m with FUNCS := []} with START := none })⟩)
          0 (.success (.of free)) n₁ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
          n₁ (.success (.of c)) n₂ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
          n₂ (.success (.of c₀)) n₃ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Imports_ok c₀ m.IMPORTS⟩)
          n₃ (.success (.of c₁)) n₄ := by
  intro h
  obtain ⟨finalSupply, hclause⟩ := module_ok_clause_success m h
  cases hclause with
  | bind_success hfree htail =>
      cases htail with
      | bind_success hcontext htail =>
          cases htail with
          | bind_success htypes htail =>
              cases htail with
              | bind_success himports _ =>
                  exact ⟨_, _, _, _, _, _, _, _, hfree, hcontext, htypes, himports⟩

theorem module_ok_funcs_success (m : SpecTec.module) :
    SpecTec.Module_ok m →
      ∃ (free : SpecTec.free) (c c₀ c₁ c₂ : SpecTec.context)
        (n₁ n₂ n₃ n₄ n₅ : Nat),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
            ({ {m with FUNCS := []} with START := none })⟩)
          0 (.success (.of free)) n₁ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
          n₁ (.success (.of c)) n₂ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
          n₂ (.success (.of c₀)) n₃ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Imports_ok c₀ m.IMPORTS⟩)
          n₃ (.success (.of c₁)) n₄ ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Funcs_ok c₁ m.FUNCS⟩)
          n₄ (.success (.of c₂)) n₅ := by
  intro h
  obtain ⟨finalSupply, hclause⟩ := module_ok_clause_success m h
  cases hclause with
  | bind_success hfree htail =>
      cases htail with
      | bind_success hcontext htail =>
          cases htail with
          | bind_success htypes htail =>
              cases htail with
              | bind_success himports htail =>
                  cases htail with
                  | bind_success hfuncs _ =>
                      exact ⟨_, _, _, _, _, _, _, _, _, _, hfree, hcontext,
                        htypes, himports, hfuncs⟩

theorem module_ok_iff_clause_success (m : SpecTec.module) :
    SpecTec.Module_ok m ↔
      ∃ finalSupply : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Module_ok:clause:0» m) 0
          (.success (.of ())) finalSupply := by
  constructor
  · exact module_ok_clause_success m
  · rintro ⟨finalSupply, hclause⟩
    exact ⟨finalSupply, .call (.orElse_success hclause)⟩

/-- The successful calls made by the generated `Module_ok` clause, in order. -/
structure ModuleOkTrace (m : SpecTec.module) : Type where
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
  free_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
      ({ {m with FUNCS := []} with START := none })⟩)
    0 (.success (.of free)) n1
  empty_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
    n1 (.success (.of c)) n2
  types_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Types_ok
      {c with REFS := free} m.TYPES⟩)
    n2 (.success (.of c0)) n3
  imports_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok c0 m.IMPORTS⟩)
    n3 (.success (.of c1)) n4
  funcs_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Funcs_ok c1 m.FUNCS⟩)
    n4 (.success (.of c2)) n5
  tables_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c2 m.TABLES⟩)
    n5 (.success (.of c3)) n6
  mems_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Mems_ok c3 m.MEMS⟩)
    n6 (.success (.of c4)) n7
  globals_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Globals_ok c4 m.GLOBALS⟩)
    n7 (.success (.of c5)) n8
  tags_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Tags_ok c5 m.TAGS⟩)
    n8 (.success (.of c6)) n9
  elems_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Elems_ok c6 m.ELEMS⟩)
    n9 (.success (.of c7)) n10
  datas_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.context, SpecTec.Call.Datas_ok c7 m.DATAS⟩)
    n10 (.success (.of c8)) n11
  funcs_second_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨Unit, SpecTec.Call.«Module_ok:rule:iter:2» c8 m.FUNCS⟩)
    n11 (.success (.of ())) n12
  start_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨Unit, SpecTec.Call.Start_ok c8 m.START⟩)
    n12 (.success (.of ())) n13
  exports_ok : SpecTecExecution.Eval SpecTec.Body
    (.call ⟨SpecTec.nameset, SpecTec.Call.Exports_ok c8
      (SpecTec.set.«`{ % `}» ([] : List SpecTec.name)) m.EXPORTS⟩)
    n13 (.success (.of names)) n14

theorem module_ok_full_trace (m : SpecTec.module) :
    SpecTec.Module_ok m → Nonempty (ModuleOkTrace m) := by
  intro h
  obtain ⟨_, hclause⟩ := module_ok_clause_success m h
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

theorem module_ok_of_full_trace (m : SpecTec.module) :
    Nonempty (ModuleOkTrace m) → SpecTec.Module_ok m := by
  rintro ⟨trace⟩
  apply (module_ok_iff_clause_success m).2
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

end properties.wasm_module_ok.Validity
