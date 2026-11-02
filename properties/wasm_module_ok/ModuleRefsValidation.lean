import properties.wasm_module_ok.TypeRefsValidation
import properties.wasm_module_ok.DeclarationRefsValidation
import properties.wasm_module_ok.Validity
import properties.wasm_module_ok.FreeModuleValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ModuleRefsValidation

open properties.wasm_module_ok
open properties.wasm_module_ok.FreeUnionValidation

theorem module_trace_refs (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) :
    tr.c0.REFS = tr.free ∧
    tr.c1.REFS = tr.free ∧
    tr.c2.REFS = tr.free ∧
    tr.c3.REFS = tr.free ∧
    tr.c4.REFS = tr.free ∧
    tr.c5.REFS = tr.free ∧
    tr.c6.REFS = tr.free ∧
    tr.c7.REFS = tr.free ∧
    tr.c8.REFS = tr.free := by
  have h0 : tr.c0.REFS = tr.free :=
    TypeRefsValidation.types_ok_refs
      {tr.c with REFS := tr.free} tr.c0 m.TYPES tr.n2 tr.n3 tr.types_ok
  have h1 : tr.c1.REFS = tr.free :=
    (ContextRefsValidation.imports_ok_refs
      tr.c0 tr.c1 m.IMPORTS tr.n3 tr.n4 tr.imports_ok).trans h0
  have h2 : tr.c2.REFS = tr.free :=
    (ContextRefsValidation.funcs_ok_refs
      tr.c1 tr.c2 m.FUNCS tr.n4 tr.n5 tr.funcs_ok).trans h1
  have h3 : tr.c3.REFS = tr.free :=
    (DeclarationRefsValidation.tables_ok_refs
      tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok).trans h2
  have h4 : tr.c4.REFS = tr.free :=
    (ContextRefsValidation.mems_ok_refs
      tr.c3 tr.c4 m.MEMS tr.n6 tr.n7 tr.mems_ok).trans h3
  have h5 : tr.c5.REFS = tr.free :=
    (DeclarationRefsValidation.globals_ok_refs
      tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8 tr.globals_ok).trans h4
  have h6 : tr.c6.REFS = tr.free :=
    (ContextRefsValidation.tags_ok_refs
      tr.c5 tr.c6 m.TAGS tr.n8 tr.n9 tr.tags_ok).trans h5
  have h7 : tr.c7.REFS = tr.free :=
    (DeclarationRefsValidation.elems_ok_refs
      tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok).trans h6
  have h8 : tr.c8.REFS = tr.free :=
    (DeclarationRefsValidation.datas_ok_refs
      tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok).trans h7
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem in_set_func_true_of_hasFunc
    (f : SpecTec.free) (x : SpecTec.funcidx) (n : Nat)
    (h : HasFunc f x) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x f.FUNCS⟩)
      n (.success (.of true)) n := by
  cases hs : f.FUNCS with
  | «`{ % `}» xs =>
    have hx : x ∈ xs := by simpa only [HasFunc, hs] using h
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$in_set_clauses» SpecTec.funcidx x
          (SpecTec.set.«`{ % `}» xs)) ())
      n (.success (.of true)) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$in_set:clause:0» SpecTec.funcidx x
        (SpecTec.set.«`{ % `}» xs))
      n (.success (.of true)) n
    simpa [SpecTec.«$in_set:clause:0», hx] using
      (SpecTecExecution.Eval.pure true :
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.pure true) n (.success (.of true)) n)

theorem module_trace_global_ref_in_context
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (g : SpecTec.global) (x : SpecTec.funcidx)
    (hg : g ∈ m.GLOBALS)
    (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT) :
    HasFunc tr.c4.REFS x := by
  have h4 := (module_trace_refs m tr).2.2.2.2.1
  rw [h4]
  exact FreeModuleValidation.free_module_global_ref_func
    ({{m with FUNCS := []} with START := none}) g x
    tr.free 0 tr.n1 (by simpa using hg) href tr.free_ok

theorem module_trace_table_ref_in_context
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (t : SpecTec.table) (x : SpecTec.funcidx)
    (ht : t ∈ m.TABLES)
    (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT) :
    HasFunc tr.c2.REFS x := by
  have h2 := (module_trace_refs m tr).2.2.1
  rw [h2]
  exact FreeModuleValidation.free_module_table_ref_func
    ({{m with FUNCS := []} with START := none}) t x
    tr.free 0 tr.n1 (by simpa using ht) href tr.free_ok

theorem module_trace_global_ref_guard
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (g : SpecTec.global) (x : SpecTec.funcidx) (n : Nat)
    (hg : g ∈ m.GLOBALS)
    (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x tr.c4.REFS.FUNCS⟩)
      n (.success (.of true)) n :=
  in_set_func_true_of_hasFunc tr.c4.REFS x n
    (module_trace_global_ref_in_context m tr g x hg href)

theorem module_trace_table_ref_guard
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (t : SpecTec.table) (x : SpecTec.funcidx) (n : Nat)
    (ht : t ∈ m.TABLES)
    (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x tr.c2.REFS.FUNCS⟩)
      n (.success (.of true)) n :=
  in_set_func_true_of_hasFunc tr.c2.REFS x n
    (module_trace_table_ref_in_context m tr t x ht href)

theorem module_trace_elem_init_ref_guard
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (e : SpecTec.elem) (init : SpecTec.const)
    (x : SpecTec.funcidx) (n : Nat)
    (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
    (href : SpecTec.instr.«REF.FUNC» x ∈ init) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x tr.c6.REFS.FUNCS⟩)
      n (.success (.of true)) n := by
  have h6 := (module_trace_refs m tr).2.2.2.2.2.2.1
  rw [h6]
  apply in_set_func_true_of_hasFunc
  exact FreeModuleValidation.free_module_elem_init_ref_func
    ({{m with FUNCS := []} with START := none}) e init x
    tr.free 0 tr.n1 (by simpa using he) hinit href tr.free_ok

theorem module_trace_elem_offset_ref_guard
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (e : SpecTec.elem) (a : SpecTec.active)
    (x : SpecTec.funcidx) (n : Nat)
    (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x tr.c6.REFS.FUNCS⟩)
      n (.success (.of true)) n := by
  have h6 := (module_trace_refs m tr).2.2.2.2.2.2.1
  rw [h6]
  apply in_set_func_true_of_hasFunc
  exact FreeModuleValidation.free_module_elem_offset_ref_func
    ({{m with FUNCS := []} with START := none}) e a x
    tr.free 0 tr.n1 (by simpa using he) hmode href tr.free_ok

theorem module_trace_data_offset_ref_guard
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (d : SpecTec.data) (a : SpecTec.active)
    (x : SpecTec.funcidx) (n : Nat)
    (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x tr.c7.REFS.FUNCS⟩)
      n (.success (.of true)) n := by
  have h7 := (module_trace_refs m tr).2.2.2.2.2.2.2.1
  rw [h7]
  apply in_set_func_true_of_hasFunc
  exact FreeModuleValidation.free_module_data_offset_ref_func
    ({{m with FUNCS := []} with START := none}) d a x
    tr.free 0 tr.n1 (by simpa using hd) hmode href tr.free_ok

end properties.wasm_module_ok.ModuleRefsValidation
