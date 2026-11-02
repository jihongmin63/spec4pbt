import properties.wasm_module_ok.ConstNumericProduction
import properties.wasm_module_ok.ConstVectorProduction
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstLiteralProduction

def literalSeed (u : SpecTec.valtype) : Bool :=
  ConstNumericProduction.numericSeed u ||
    ConstVectorProduction.vectorSeed u

/-- The finite nullary literal base, drawn from the proven candidate universe. -/
def literalBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => literalSeed u = true)

theorem literal_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ literalBase c ↔ literalSeed u = true := by
  simp only [literalBase, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hseed
    refine ⟨?_, hseed⟩
    cases u with
    | NumT nt =>
        exact FiniteValidTypes.valid_mem_candidateUniverse
          c (.NumT nt) (by cases nt <;> rfl)
    | VecT vt =>
        exact FiniteValidTypes.valid_mem_candidateUniverse
          c (.VecT vt) (by cases vt <;> rfl)
    | RefT _ => simp [literalSeed,
        ConstNumericProduction.numericSeed,
        ConstVectorProduction.vectorSeed] at hseed
    | BotT => simp [literalSeed,
        ConstNumericProduction.numericSeed,
        ConstVectorProduction.vectorSeed] at hseed

theorem literal_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    literalSeed u = true ↔
      (∃ v : SpecTec.num_,
        ConstSyntaxDecision.syntaxAllowed c (.CONST v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.CONST v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n) ∨
      (∃ v : SpecTec.vec_,
        ConstSyntaxDecision.syntaxAllowed c (.«VEC.CONST» v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«VEC.CONST» v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n) := by
  rw [literalSeed, Bool.or_eq_true,
    ConstNumericProduction.numeric_seed_iff_instr_effect,
    ConstVectorProduction.vector_seed_iff_instr_effect]

theorem literal_base_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    u ∈ literalBase c ↔
      (∃ v : SpecTec.num_,
        ConstSyntaxDecision.syntaxAllowed c (.CONST v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.CONST v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n) ∨
      (∃ v : SpecTec.vec_,
        ConstSyntaxDecision.syntaxAllowed c (.«VEC.CONST» v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«VEC.CONST» v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n) := by
  rw [literal_base_mem_iff, literal_seed_iff_instr_effect]

end properties.wasm_module_ok.ConstLiteralProduction
