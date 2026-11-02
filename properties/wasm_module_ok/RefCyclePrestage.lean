import properties.wasm_module_ok.RefCycleUniversal

set_option autoImplicit false

namespace properties.wasm_module_ok.RefCyclePrestage

inductive DirectSyntax (m : SpecTec.module) : SpecTec.funcidx → Prop where
  | table (t : SpecTec.table) (x : SpecTec.funcidx)
      (ht : t ∈ m.TABLES)
      (href : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT) : DirectSyntax m x
  | global (g : SpecTec.global) (x : SpecTec.funcidx)
      (hg : g ∈ m.GLOBALS)
      (href : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT) : DirectSyntax m x
  | elemInit (e : SpecTec.elem) (init : SpecTec.const)
      (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
      (href : SpecTec.instr.«REF.FUNC» x ∈ init) : DirectSyntax m x
  | elemOffset (e : SpecTec.elem) (a : SpecTec.active)
      (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
      (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) : DirectSyntax m x
  | dataOffset (d : SpecTec.data) (a : SpecTec.active)
      (x : SpecTec.funcidx)
      (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
      (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) : DirectSyntax m x

theorem direct_hasFunc_free
    (m : SpecTec.module) (free : SpecTec.free)
    (n : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
        ({{m with FUNCS := []} with START := none})⟩)
      0 (.success (.of free)) n)
    (x : SpecTec.funcidx) (hocc : DirectSyntax m x) :
    FreeUnionValidation.HasFunc free x := by
  cases hocc with
  | table t x ht href =>
      exact FreeModuleValidation.free_module_table_ref_func
        ({{m with FUNCS := []} with START := none}) t x free 0 n
        (by simpa using ht) href hfree
  | global g x hg href =>
      exact FreeModuleValidation.free_module_global_ref_func
        ({{m with FUNCS := []} with START := none}) g x free 0 n
        (by simpa using hg) href hfree
  | elemInit e init x he hinit href =>
      exact FreeModuleValidation.free_module_elem_init_ref_func
        ({{m with FUNCS := []} with START := none}) e init x free 0 n
        (by simpa using he) hinit href hfree
  | elemOffset e a x he hmode href =>
      exact FreeModuleValidation.free_module_elem_offset_ref_func
        ({{m with FUNCS := []} with START := none}) e a x free 0 n
        (by simpa using he) hmode href hfree
  | dataOffset d a x hd hmode href =>
      exact FreeModuleValidation.free_module_data_offset_ref_func
        ({{m with FUNCS := []} with START := none}) d a x free 0 n
        (by simpa using hd) hmode href hfree

theorem direct_instr_ok_iff_bound
    (m : SpecTec.module) (free : SpecTec.free)
    (nfree : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module»
        ({{m with FUNCS := []} with START := none})⟩)
      0 (.success (.of free)) nfree)
    (c : SpecTec.context) (hrefs : c.REFS = free)
    (x : SpecTec.funcidx) (hocc : DirectSyntax m x)
    (irt : SpecTec.inferresulttype) (n : Nat) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < c.FUNCS.length := by
  constructor
  · rintro ⟨result, finalSupply, hcall⟩
    exact (InstrRefDispatch.ref_func_dispatch_requires_membership
      c irt x result n finalSupply hcall).1
  · intro hlt
    have hget : c.FUNCS[x]? = some c.FUNCS[x] :=
      List.getElem?_eq_getElem hlt
    have hmember : FreeUnionValidation.HasFunc c.REFS x := by
      rw [hrefs]
      exact direct_hasFunc_free m free nfree hfree x hocc
    obtain ⟨result, hcall⟩ :=
      InstrRefDispatch.ref_func_dispatch_success_of_membership
        c irt x c.FUNCS[x] n hlt hget hmember
    exact ⟨result, n, hcall⟩

end properties.wasm_module_ok.RefCyclePrestage
