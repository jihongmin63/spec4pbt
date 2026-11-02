import properties.wasm_module_ok.FreeListValidation
import properties.wasm_module_ok.Validity
import properties.wasm_module_ok.FreeElemValidation
import properties.wasm_module_ok.FreeOffsetValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeModuleValidation

open properties.wasm_module_ok.FreeUnionValidation
open properties.wasm_module_ok.FreeListValidation

structure FreeModuleTrace (m : SpecTec.module)
    (result : SpecTec.free) (start finalSupply : Nat) : Type where
  f1 : SpecTec.free
  f2 : SpecTec.free
  f3 : SpecTec.free
  f4 : SpecTec.free
  f5 : SpecTec.free
  f6 : SpecTec.free
  f7 : SpecTec.free
  f8 : SpecTec.free
  f9 : SpecTec.free
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n5 : Nat
  n6 : Nat
  n7 : Nat
  n9 : Nat
  globals : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free,
      SpecTec.SpecTecCall.«$free_list» SpecTec.global
        SpecTec.SpecTecCall.«$free_global» m.GLOBALS⟩)
    n1 (.success (.of f2)) n2
  tables : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free,
      SpecTec.SpecTecCall.«$free_list» SpecTec.table
        SpecTec.SpecTecCall.«$free_table» m.TABLES⟩)
    n2 (.success (.of f3)) n3
  elems : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free,
      SpecTec.SpecTecCall.«$free_list» SpecTec.elem
        SpecTec.SpecTecCall.«$free_elem» m.ELEMS⟩)
    n5 (.success (.of f6)) n6
  datas : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free,
      SpecTec.SpecTecCall.«$free_list» SpecTec.data
        SpecTec.SpecTecCall.«$free_data» m.DATAS⟩)
    n6 (.success (.of f7)) n7
  unions : SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨SpecTec.free,
      SpecTec.SpecTecCall.«$free_unions»
        [f1, f2, f3, f4, f5, f6, f7, f8, f9]⟩)
    n9 (.success (.of result)) finalSupply

theorem free_module_trace (m : SpecTec.module)
    (result : SpecTec.free) (start finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) :
    Nonempty (FreeModuleTrace m result start finalSupply) := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$free_module_clauses» m) ())
      start (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_module:clause:0» at hclause
      cases hclause with
      | bind_success htypes htail =>
        rename_i n1 f1
        cases htail with
        | bind_success hglobals htail =>
          rename_i n2 f2
          cases htail with
          | bind_success htables htail =>
            rename_i n3 f3
            cases htail with
            | bind_success hmems htail =>
              rename_i n4 f4
              cases htail with
              | bind_success hstart htail =>
                rename_i n5 f5
                cases htail with
                | bind_success helems htail =>
                  rename_i n6 f6
                  cases htail with
                  | bind_success hdatas htail =>
                    rename_i n7 f7
                    cases htail with
                    | bind_success himports htail =>
                      rename_i n8 f8
                      cases htail with
                      | bind_success hexports htail =>
                        rename_i n9 f9
                        cases htail with
                        | bind_success hunions hpure =>
                          cases hpure with
                          | pure =>
                            exact ⟨{
                              f1 := f1, f2 := f2, f3 := f3,
                              f4 := f4, f5 := f5, f6 := f6,
                              f7 := f7, f8 := f8, f9 := f9,
                              n1 := n1, n2 := n2, n3 := n3,
                              n5 := n5, n6 := n6, n7 := n7, n9 := n9,
                              globals := hglobals, tables := htables,
                              elems := helems, datas := hdatas,
                              unions := hunions
                            }⟩
    | orElse_unmatch _ hnone => cases hnone

theorem free_module_global_ref_func
    (m : SpecTec.module) (g : SpecTec.global)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (start finalSupply : Nat)
    (hg : g ∈ m.GLOBALS)
    (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) : HasFunc result x := by
  obtain ⟨trace⟩ := free_module_trace m result start finalSupply hcall
  have hcomponent : HasFunc trace.f2 x :=
    free_globals_ref_func m.GLOBALS g x trace.f2 trace.n1 trace.n2
      hg href trace.globals
  exact free_unions_preserves_funcs
    [trace.f1, trace.f2, trace.f3, trace.f4, trace.f5,
      trace.f6, trace.f7, trace.f8, trace.f9]
    result trace.f2 x trace.n9 finalSupply trace.unions
    (by simp) hcomponent

theorem free_module_table_ref_func
    (m : SpecTec.module) (t : SpecTec.table)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (start finalSupply : Nat)
    (ht : t ∈ m.TABLES)
    (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) : HasFunc result x := by
  obtain ⟨trace⟩ := free_module_trace m result start finalSupply hcall
  have hcomponent : HasFunc trace.f3 x :=
    free_tables_ref_func m.TABLES t x trace.f3 trace.n2 trace.n3
      ht href trace.tables
  exact free_unions_preserves_funcs
    [trace.f1, trace.f2, trace.f3, trace.f4, trace.f5,
      trace.f6, trace.f7, trace.f8, trace.f9]
    result trace.f3 x trace.n9 finalSupply trace.unions
    (by simp) hcomponent

theorem free_module_elem_init_ref_func
    (m : SpecTec.module) (e : SpecTec.elem)
    (init : SpecTec.const) (x : SpecTec.funcidx)
    (result : SpecTec.free) (start finalSupply : Nat)
    (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
    (href : SpecTec.instr.«REF.FUNC» x ∈ init)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) : HasFunc result x := by
  obtain ⟨trace⟩ := free_module_trace m result start finalSupply hcall
  have hcomponent : HasFunc trace.f6 x :=
    FreeElemValidation.free_elems_init_ref_func
      m.ELEMS e init x trace.f6 trace.n5 trace.n6
      he hinit href trace.elems
  exact free_unions_preserves_funcs
    [trace.f1, trace.f2, trace.f3, trace.f4, trace.f5,
      trace.f6, trace.f7, trace.f8, trace.f9]
    result trace.f6 x trace.n9 finalSupply trace.unions
    (by simp) hcomponent

theorem free_module_elem_offset_ref_func
    (m : SpecTec.module) (e : SpecTec.elem)
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (start finalSupply : Nat)
    (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) : HasFunc result x := by
  obtain ⟨trace⟩ := free_module_trace m result start finalSupply hcall
  have hcomponent : HasFunc trace.f6 x :=
    FreeOffsetValidation.free_elems_active_offset_ref_func
      m.ELEMS e a x trace.f6 trace.n5 trace.n6
      he hmode href trace.elems
  exact free_unions_preserves_funcs
    [trace.f1, trace.f2, trace.f3, trace.f4, trace.f5,
      trace.f6, trace.f7, trace.f8, trace.f9]
    result trace.f6 x trace.n9 finalSupply trace.unions
    (by simp) hcomponent

theorem free_module_data_offset_ref_func
    (m : SpecTec.module) (d : SpecTec.data)
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (start finalSupply : Nat)
    (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_module» m⟩)
      start (.success (.of result)) finalSupply) : HasFunc result x := by
  obtain ⟨trace⟩ := free_module_trace m result start finalSupply hcall
  have hcomponent : HasFunc trace.f7 x :=
    FreeOffsetValidation.free_datas_active_offset_ref_func
      m.DATAS d a x trace.f7 trace.n6 trace.n7
      hd hmode href trace.datas
  exact free_unions_preserves_funcs
    [trace.f1, trace.f2, trace.f3, trace.f4, trace.f5,
      trace.f6, trace.f7, trace.f8, trace.f9]
    result trace.f7 x trace.n9 finalSupply trace.unions
    (by simp) hcomponent

theorem module_ok_global_ref_in_free
    (m : SpecTec.module) (g : SpecTec.global) (x : SpecTec.funcidx)
    (hmodule : SpecTec.Module_ok m)
    (hg : g ∈ m.GLOBALS)
    (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT) :
    ∃ (free : SpecTec.free) (n : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.free,
          SpecTec.SpecTecCall.«$free_module»
            ({{m with FUNCS := []} with START := none})⟩)
        0 (.success (.of free)) n ∧ HasFunc free x := by
  obtain ⟨trace⟩ := Validity.module_ok_full_trace m hmodule
  refine ⟨trace.free, trace.n1, trace.free_ok, ?_⟩
  exact free_module_global_ref_func
    ({{m with FUNCS := []} with START := none}) g x
    trace.free 0 trace.n1 (by simpa using hg) href trace.free_ok

theorem module_ok_table_ref_in_free
    (m : SpecTec.module) (t : SpecTec.table) (x : SpecTec.funcidx)
    (hmodule : SpecTec.Module_ok m)
    (ht : t ∈ m.TABLES)
    (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT) :
    ∃ (free : SpecTec.free) (n : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.free,
          SpecTec.SpecTecCall.«$free_module»
            ({{m with FUNCS := []} with START := none})⟩)
        0 (.success (.of free)) n ∧ HasFunc free x := by
  obtain ⟨trace⟩ := Validity.module_ok_full_trace m hmodule
  refine ⟨trace.free, trace.n1, trace.free_ok, ?_⟩
  exact free_module_table_ref_func
    ({{m with FUNCS := []} with START := none}) t x
    trace.free 0 trace.n1 (by simpa using ht) href trace.free_ok

end properties.wasm_module_ok.FreeModuleValidation
