import properties.wasm_module_ok.ConstStepDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFoldDecision

/-- Run the exact constant-instruction stack transition over a list.  The
available stack is the state; no bound on its length is imposed. -/
def constantFoldResult (c : SpecTec.context) :
    List SpecTec.valtype → List SpecTec.instr →
      Option SpecTec.inferresulttype
  | available, [] => some (.NoEllipses, available)
  | available, i :: rest => do
      let pushed ← ConstStepDecision.constantStepResult c available i
      match pushed with
      | (.NoEllipses, next) => constantFoldResult c next rest
      | _ => none

theorem constant_fold_cons_iff
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (rest : List SpecTec.instr)
    (result : SpecTec.inferresulttype) :
    constantFoldResult c available (i :: rest) = some result ↔
      ∃ next : List SpecTec.valtype,
        ConstStepDecision.constantStepResult c available i =
          some (.NoEllipses, next) ∧
        constantFoldResult c next rest = some result := by
  constructor
  · intro h
    unfold constantFoldResult at h
    cases hs : ConstStepDecision.constantStepResult c available i with
    | none => simp [hs] at h
    | some pushed =>
        cases pushed with
        | mk dots next =>
            cases dots with
            | Ellipses => simp [hs] at h
            | NoEllipses =>
                exact ⟨next, rfl, by simpa [hs] using h⟩
  · rintro ⟨next, hs, hrest⟩
    simp [constantFoldResult, hs, hrest]

theorem constant_fold_result_concrete_stack
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (xs : List SpecTec.instr) (result : SpecTec.inferresulttype)
    (h : constantFoldResult c available xs = some result) :
    ∃ finalStack : List SpecTec.valtype,
      result = (.NoEllipses, finalStack) := by
  induction xs generalizing available with
  | nil =>
      simp only [constantFoldResult, Option.some.injEq] at h
      exact ⟨available, h.symm⟩
  | cons i rest ih =>
      obtain ⟨next, _, hrest⟩ :=
        (constant_fold_cons_iff c available i rest result).1 h
      exact ih next hrest

theorem constant_fold_success_all_allowed
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (xs : List SpecTec.instr) (result : SpecTec.inferresulttype)
    (h : constantFoldResult c available xs = some result) :
    ∀ i ∈ xs, ConstSyntaxDecision.syntaxAllowed c i = true := by
  induction xs generalizing available with
  | nil =>
      intro i hmem
      cases hmem
  | cons head rest ih =>
      obtain ⟨next, hstep, hrest⟩ :=
        (constant_fold_cons_iff c available head rest result).1 h
      obtain ⟨iit, need, popped, hi, _, _, _⟩ :=
        (ConstStepDecision.constant_step_result_iff_components
          c available head (.NoEllipses, next)).1 hstep
      have hhead :=
        ((ConstInstrDecision.constant_instruction_result_iff
          c (.NoEllipses, available) head iit 0 0).1
          ⟨hi, rfl⟩).1
      intro i hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact hhead
      · exact ih next hrest i htail

end properties.wasm_module_ok.ConstFoldDecision
