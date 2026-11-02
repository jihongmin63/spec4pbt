import properties.wasm_module_ok.InstrRefDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.RefCycleDirect

inductive Occurs (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) : SpecTec.context → SpecTec.funcidx → Prop where
  | global (g : SpecTec.global) (x : SpecTec.funcidx)
      (hg : g ∈ m.GLOBALS)
      (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT) : Occurs m tr tr.c4 x
  | table (t : SpecTec.table) (x : SpecTec.funcidx)
      (ht : t ∈ m.TABLES)
      (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT) : Occurs m tr tr.c2 x
  | elemInit (e : SpecTec.elem) (init : SpecTec.const)
      (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
      (href : SpecTec.instr.«REF.FUNC» x ∈ init) : Occurs m tr tr.c6 x
  | elemOffset (e : SpecTec.elem) (a : SpecTec.active)
      (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
      (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) : Occurs m tr tr.c6 x
  | dataOffset (d : SpecTec.data) (a : SpecTec.active)
      (x : SpecTec.funcidx)
      (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
      (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) : Occurs m tr tr.c7 x

theorem occurs_guard (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) (c : SpecTec.context)
    (x : SpecTec.funcidx) (n : Nat) (h : Occurs m tr c x) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$in_set»
        SpecTec.funcidx x c.REFS.FUNCS⟩)
      n (.success (.of true)) n := by
  cases h with
  | global g x hg href =>
      exact ModuleRefsValidation.module_trace_global_ref_guard
        m tr g x n hg href
  | table t x ht href =>
      exact ModuleRefsValidation.module_trace_table_ref_guard
        m tr t x n ht href
  | elemInit e init x he hinit href =>
      exact ModuleRefsValidation.module_trace_elem_init_ref_guard
        m tr e init x n he hinit href
  | elemOffset e a x he hmode href =>
      exact ModuleRefsValidation.module_trace_elem_offset_ref_guard
        m tr e a x n he hmode href
  | dataOffset d a x hd hmode href =>
      exact ModuleRefsValidation.module_trace_data_offset_ref_guard
        m tr d a x n hd hmode href

theorem instr_ok_iff_bound (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) (c : SpecTec.context)
    (x : SpecTec.funcidx) (irt : SpecTec.inferresulttype)
    (n : Nat) (hocc : Occurs m tr c x) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < c.FUNCS.length := by
  constructor
  · rintro ⟨result, finalSupply, hcall⟩
    exact (InstrRefDispatch.ref_func_dispatch_requires_membership
      c irt x result n finalSupply hcall).1
  · intro hlt
    have hget : c.FUNCS[x]? = some c.FUNCS[x] :=
      List.getElem?_eq_getElem hlt
    have href : FreeUnionValidation.HasFunc c.REFS x :=
      RefFuncValidation.hasFunc_of_in_set_true c.REFS x n n
        (occurs_guard m tr c x n hocc)
    obtain ⟨result, hcall⟩ :=
      InstrRefDispatch.ref_func_dispatch_success_of_membership
        c irt x c.FUNCS[x] n hlt hget href
    exact ⟨result, n, hcall⟩

end properties.wasm_module_ok.RefCycleDirect
