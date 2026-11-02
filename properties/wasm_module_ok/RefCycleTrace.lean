import properties.wasm_module_ok.DeclarationConstValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RefCycleTrace

theorem table_ref_occurs_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (t : SpecTec.table) (i : SpecTec.instr) (x : SpecTec.funcidx)
    (ht : t ∈ m.TABLES) (hi : i ∈ t.TINIT)
    (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ t.TINIT := by
  obtain ⟨c, vt, start, finish, hconst⟩ :=
    DeclarationConstValidation.tables_ok_member_const
      tr.c2 tr.c3 m.TABLES t tr.n5 tr.n6 tr.tables_ok ht
  exact ConstNestedValidation.const_ok_ref_occurs_direct
    c vt t.TINIT start finish hconst i x hi hocc

theorem global_ref_occurs_direct
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (g : SpecTec.global) (i : SpecTec.instr) (x : SpecTec.funcidx)
    (hg : g ∈ m.GLOBALS) (hi : i ∈ g.GINIT)
    (hocc : ConstNestedValidation.RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ g.GINIT := by
  obtain ⟨c, vt, start, finish, hconst⟩ :=
    DeclarationConstValidation.globals_ok_member_const
      tr.c4 tr.c5 m.GLOBALS g tr.n7 tr.n8 tr.globals_ok hg
  exact ConstNestedValidation.const_ok_ref_occurs_direct
    c vt g.GINIT start finish hconst i x hi hocc

theorem table_instr_ok_iff_bound
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (t : SpecTec.table) (i : SpecTec.instr) (x : SpecTec.funcidx)
    (irt : SpecTec.inferresulttype) (n : Nat)
    (ht : t ∈ m.TABLES) (hi : i ∈ t.TINIT)
    (hocc : ConstNestedValidation.RefOccurs i x) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok tr.c2 irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < tr.c2.FUNCS.length :=
  RefCycleDirect.instr_ok_iff_bound m tr tr.c2 x irt n
    (.table t x ht (table_ref_occurs_direct m tr t i x ht hi hocc))

theorem global_instr_ok_iff_bound
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (g : SpecTec.global) (i : SpecTec.instr) (x : SpecTec.funcidx)
    (irt : SpecTec.inferresulttype) (n : Nat)
    (hg : g ∈ m.GLOBALS) (hi : i ∈ g.GINIT)
    (hocc : ConstNestedValidation.RefOccurs i x) :
    (∃ (result : SpecTec.inferinstrtype) (finalSupply : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok tr.c4 irt (.«REF.FUNC» x)⟩)
        n (.success (.of result)) finalSupply) ↔
      x < tr.c4.FUNCS.length :=
  RefCycleDirect.instr_ok_iff_bound m tr tr.c4 x irt n
    (.global g x hg (global_ref_occurs_direct m tr g i x hg hi hocc))

end properties.wasm_module_ok.RefCycleTrace
