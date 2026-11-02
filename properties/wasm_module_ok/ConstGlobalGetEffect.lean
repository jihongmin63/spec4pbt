import properties.wasm_module_ok.ConstRefNullDispatch
import properties.wasm_module_ok.ConstGlobalGetValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstGlobalGetEffect

theorem global_get_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (m : SpecTec.«mut»)
    (t : SpecTec.valtype) (n : Nat)
    (hget : c.GLOBALS[x]? = some (.GlobalT m t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:28» c irt (.«GLOBAL.GET» x))
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [t]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:28»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  rw [hget]
  exact SpecTecExecution.Eval.pure _

theorem global_get_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:28» c irt (.«GLOBAL.GET» x))
      n (.success (.of iit)) fin) :
    ∃ m : SpecTec.«mut», ∃ t : SpecTec.valtype,
      c.GLOBALS[x]? = some (.GlobalT m t) ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [t]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
      fin = n := by
  have hget : ∃ m : SpecTec.«mut», ∃ t : SpecTec.valtype,
      c.GLOBALS[x]? = some (.GlobalT m t) := by
    unfold SpecTec.«Instr_ok:clause:28» at h
    cases h with
    | bind_success _ htail =>
        cases htail with
        | bind_success _ htail =>
            cases hg : c.GLOBALS[x]? with
            | none =>
                rw [hg] at htail
                cases htail
            | some gt =>
                cases gt with
                | GlobalT m t => exact ⟨m, t, rfl⟩
  obtain ⟨m, t, hget⟩ := hget
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request a b hp
    cases hp
  obtain ⟨hout, hsupply⟩ :=
    SpecTecExecution.eval_deterministic hdet h
      (global_get_clause_total c irt x m t n hget)
  cases hout
  exact ⟨m, t, hget, rfl, hsupply⟩

end properties.wasm_module_ok.ConstGlobalGetEffect
