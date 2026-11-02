import properties.wasm_module_ok.InstrRefDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefFuncEffect

theorem ref_func_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (dt : SpecTec.deftype) (n : Nat)
    (hget : c.FUNCS[x]? = some dt)
    (href : FreeUnionValidation.HasFunc c.REFS x) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:51»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  simp only [hget]
  apply SpecTecExecution.Eval.bind_success
    (ModuleRefsValidation.in_set_func_true_of_hasFunc c.REFS x n href)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure _

theorem ref_func_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
      n (.success (.of iit)) fin) :
    ∃ dt : SpecTec.deftype,
      c.FUNCS[x]? = some dt ∧
      FreeUnionValidation.HasFunc c.REFS x ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
      fin = n := by
  obtain ⟨hlt, href⟩ :=
    RefFuncValidation.ref_func_clause_requires_membership c irt x iit n fin h
  have hget : c.FUNCS[x]? = some c.FUNCS[x] :=
    List.getElem?_eq_getElem hlt
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request a b hp
    cases hp
  obtain ⟨hout, hsupply⟩ :=
    SpecTecExecution.eval_deterministic hdet h
      (ref_func_clause_total c irt x c.FUNCS[x] n hget href)
  cases hout
  exact ⟨c.FUNCS[x], hget, href, rfl, hsupply⟩

theorem ref_func_instruction_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
      n (.success (.of iit)) fin ↔
    ∃ dt : SpecTec.deftype,
      c.FUNCS[x]? = some dt ∧
      FreeUnionValidation.HasFunc c.REFS x ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
      fin = n := by
  constructor
  · intro h
    exact ref_func_clause_exact c irt x iit n fin
      (InstrRefDispatch.ref_func_clause_of_dispatch c irt x iit n fin h)
  · rintro ⟨dt, hget, href, hiit, hfin⟩
    subst iit
    subst fin
    exact InstrRefDispatch.ref_func_dispatch_of_clause c irt x _ n n
      (ref_func_clause_total c irt x dt n hget href)

end properties.wasm_module_ok.ConstRefFuncEffect
