import properties.wasm_module_ok.ConstSyntaxClassification

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxListClassification

theorem iter_success_all_syntax
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (n fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Const_ok:rule:iter:0» c xs⟩)
      n (.success (.of ())) fin) :
    ∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i := by
  induction xs generalizing n fin with
  | nil =>
      intro i hmem
      simp at hmem
  | cons head rest ih =>
      obtain ⟨middle, hhead, hrest⟩ :=
        (ConstSyntaxValidation.const_iter_cons_success_iff
          c head rest n fin).1 hcall
      intro i hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · subst heq
        exact (ConstSyntaxClassification.is_const_success_iff
          c i n middle).1 hhead |>.1
      · exact ih middle fin hrest i htail

theorem iter_success_iff
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Const_ok:rule:iter:0» c xs⟩)
      n (.success (.of ())) fin ↔
    (∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i) ∧
      fin = n := by
  constructor
  · intro hcall
    have hall := iter_success_all_syntax c xs n fin hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    obtain ⟨_, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet hcall
        (ConstAdditionalSyntaxValidation.syntax_iter_total c xs n hall)
    exact ⟨hall, hsupply⟩
  · rintro ⟨hall, rfl⟩
    exact ConstAdditionalSyntaxValidation.syntax_iter_total c xs fin hall

end properties.wasm_module_ok.ConstSyntaxListClassification
