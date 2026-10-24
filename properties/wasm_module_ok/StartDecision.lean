import properties.wasm_module_ok.StartValidation
import properties.wasm_module_ok.UnrollInterface

set_option autoImplicit false

namespace properties.wasm_module_ok.StartDecision

def startValid (c : SpecTec.context) : Option SpecTec.start → Bool
  | none => true
  | some s =>
      match c.FUNCS[s.SFUNC]? with
      | none => false
      | some dt => decide (UnrollInterface.deftypeFunctype dt =
          some (SpecTec.functype.FuncT [] []))

theorem start_some_success_iff_result
    (c : SpecTec.context) (s : SpecTec.start)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c (some s)⟩)
      n (.success (.of ())) finalSupply ↔
    (∃ dt : SpecTec.deftype,
      c.FUNCS[s.SFUNC]? = some dt ∧
      UnrollInterface.deftypeFunctype dt =
        some (SpecTec.functype.FuncT [] [])) ∧
    finalSupply = n := by
  rw [StartValidation.start_some_success_iff_unrolldt]
  constructor
  · rintro ⟨dt, fin, supers, hget, hunroll⟩
    obtain ⟨hft, hsupply⟩ :=
      (UnrollInterface.unroll_functype_success_iff
        dt (.FuncT [] []) n finalSupply).1 ⟨fin, supers, hunroll⟩
    exact ⟨⟨dt, hget, hft⟩, hsupply⟩
  · rintro ⟨⟨dt, hget, hft⟩, hsupply⟩
    obtain ⟨fin, supers, hunroll⟩ :=
      (UnrollInterface.unroll_functype_success_iff
        dt (.FuncT [] []) n finalSupply).2 ⟨hft, hsupply⟩
    exact ⟨dt, fin, supers, hget, hunroll⟩

theorem start_some_valid_iff (c : SpecTec.context)
    (s : SpecTec.start) :
    startValid c (some s) = true ↔
    ∃ dt : SpecTec.deftype,
      c.FUNCS[s.SFUNC]? = some dt ∧
      UnrollInterface.deftypeFunctype dt =
        some (SpecTec.functype.FuncT [] []) := by
  constructor
  · intro h
    cases hget : c.FUNCS[s.SFUNC]? with
    | none => simp [startValid, hget] at h
    | some dt =>
      have hft : UnrollInterface.deftypeFunctype dt =
          some (SpecTec.functype.FuncT [] []) := by
        simpa [startValid, hget] using h
      exact ⟨dt, rfl, hft⟩
  · rintro ⟨dt, hget, hft⟩
    simp [startValid, hget, hft]

theorem start_success_iff_valid (c : SpecTec.context)
    (start : Option SpecTec.start) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c start⟩)
      n (.success (.of ())) finalSupply ↔
    startValid c start = true ∧ finalSupply = n := by
  cases start with
  | none =>
    constructor
    · intro h
      have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨_, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet h
          (StartValidation.start_none_success c n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, rfl⟩
      exact StartValidation.start_none_success c finalSupply
  | some s =>
    rw [start_some_success_iff_result, start_some_valid_iff]

end properties.wasm_module_ok.StartDecision
