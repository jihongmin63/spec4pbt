import properties.wasm_module_ok.ModeConstValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RefCycleUniversal

theorem elem_initializer_ref_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (e : SpecTec.elem) (init : SpecTec.const)
    (i : SpecTec.instr) (x : SpecTec.funcidx)
    (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
    (hi : i ∈ init) (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ init := by
  obtain ⟨c, produced, start, finish, helem⟩ :=
    ElemDataCallValidation.elems_ok_member_call
      tr.c6 tr.c7 m.ELEMS e tr.n9 tr.n10 tr.elems_ok he
  obtain ⟨⟨iterStart, iterFinish, hiter⟩, _⟩ :=
    ElemDataConstValidation.elem_ok_initializer_and_mode
      c produced e start finish helem
  obtain ⟨constStart, constFinish, hconst⟩ :=
    ElemDataConstValidation.elem_iter_member_const
      c e.ETYPE e.EINIT iterStart iterFinish hiter init hinit
  exact ConstNestedValidation.const_ok_ref_occurs_direct
    c (.RefT e.ETYPE) init constStart constFinish hconst i x hi hocc

theorem elem_offset_ref_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (e : SpecTec.elem) (a : SpecTec.active)
    (i : SpecTec.instr) (x : SpecTec.funcidx)
    (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
    (hi : i ∈ a.OFFSET) (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET := by
  obtain ⟨c, produced, start, finish, helem⟩ :=
    ElemDataCallValidation.elems_ok_member_call
      tr.c6 tr.c7 m.ELEMS e tr.n9 tr.n10 tr.elems_ok he
  obtain ⟨_, ⟨modeStart, modeFinish, hmodeCall⟩⟩ :=
    ElemDataConstValidation.elem_ok_initializer_and_mode
      c produced e start finish helem
  rw [hmode] at hmodeCall
  obtain ⟨vt, constStart, constFinish, hconst⟩ :=
    ModeConstValidation.elemmode_active_const
      c e.ETYPE a modeStart modeFinish hmodeCall
  exact ConstNestedValidation.const_ok_ref_occurs_direct
    c vt a.OFFSET constStart constFinish hconst i x hi hocc

theorem data_offset_ref_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (d : SpecTec.data) (a : SpecTec.active)
    (i : SpecTec.instr) (x : SpecTec.funcidx)
    (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
    (hi : i ∈ a.OFFSET) (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET := by
  obtain ⟨c, produced, start, finish, hdata⟩ :=
    ElemDataCallValidation.datas_ok_member_call
      tr.c7 tr.c8 m.DATAS d tr.n10 tr.n11 tr.datas_ok hd
  obtain ⟨modeStart, modeFinish, hmodeCall⟩ :=
    ElemDataConstValidation.data_ok_mode c produced d start finish hdata
  rw [hmode] at hmodeCall
  obtain ⟨vt, constStart, constFinish, hconst⟩ :=
    ModeConstValidation.datamode_active_const
      c a modeStart modeFinish hmodeCall
  exact ConstNestedValidation.const_ok_ref_occurs_direct
    c vt a.OFFSET constStart constFinish hconst i x hi hocc

inductive Occurs (m : SpecTec.module)
    (tr : Validity.ModuleOkTrace m) : SpecTec.context → SpecTec.funcidx → Prop where
  | table (t : SpecTec.table) (i : SpecTec.instr)
      (x : SpecTec.funcidx) (ht : t ∈ m.TABLES)
      (hi : i ∈ t.TINIT) (hocc : ConstNestedValidation.RefOccurs i x) :
      Occurs m tr tr.c2 x
  | global (g : SpecTec.global) (i : SpecTec.instr)
      (x : SpecTec.funcidx) (hg : g ∈ m.GLOBALS)
      (hi : i ∈ g.GINIT) (hocc : ConstNestedValidation.RefOccurs i x) :
      Occurs m tr tr.c4 x
  | elemInit (e : SpecTec.elem) (init : SpecTec.const)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hinit : init ∈ e.EINIT)
      (hi : i ∈ init) (hocc : ConstNestedValidation.RefOccurs i x) :
      Occurs m tr tr.c6 x
  | elemOffset (e : SpecTec.elem) (a : SpecTec.active)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (he : e ∈ m.ELEMS) (hmode : e.EMODE = .Active a)
      (hi : i ∈ a.OFFSET) (hocc : ConstNestedValidation.RefOccurs i x) :
      Occurs m tr tr.c6 x
  | dataOffset (d : SpecTec.data) (a : SpecTec.active)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hd : d ∈ m.DATAS) (hmode : d.DMODE = .Active a)
      (hi : i ∈ a.OFFSET) (hocc : ConstNestedValidation.RefOccurs i x) :
      Occurs m tr tr.c7 x

theorem occurs_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context) (x : SpecTec.funcidx)
    (h : Occurs m tr c x) : RefCycleDirect.Occurs m tr c x := by
  cases h with
  | table t i x ht hi hocc =>
      exact .table t x ht
        (RefCycleTrace.table_ref_occurs_direct m tr t i x ht hi hocc)
  | global g i x hg hi hocc =>
      exact .global g x hg
        (RefCycleTrace.global_ref_occurs_direct m tr g i x hg hi hocc)
  | elemInit e init i x he hinit hi hocc =>
      exact .elemInit e init x he hinit
        (elem_initializer_ref_direct m tr e init i x he hinit hi hocc)
  | elemOffset e a i x he hmode hi hocc =>
      exact .elemOffset e a x he hmode
        (elem_offset_ref_direct m tr e a i x he hmode hi hocc)
  | dataOffset d a i x hd hmode hi hocc =>
      exact .dataOffset d a x hd hmode
        (data_offset_ref_direct m tr d a i x hd hmode hi hocc)

theorem instr_ok_iff_bound
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context) (x : SpecTec.funcidx)
    (irt : SpecTec.inferresulttype) (n : Nat)
    (h : Occurs m tr c x) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < c.FUNCS.length :=
  RefCycleDirect.instr_ok_iff_bound m tr c x irt n
    (occurs_direct m tr c x h)

end properties.wasm_module_ok.RefCycleUniversal
