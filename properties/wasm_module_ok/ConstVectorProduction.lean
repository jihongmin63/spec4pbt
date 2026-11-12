import properties.wasm_module_ok.ConstVectorDispatch
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstVectorProduction

/-- The nullary vector production in the finite constant-type closure. -/
def vectorSeed : SpecTec.valtype → Bool
  | .VecT .V128T => true
  | _ => false

def vectorWitness : SpecTec.vec_ := .V128 0

theorem vector_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    vectorSeed u = true ↔
      ∃ v : SpecTec.vec_,
        ConstSyntaxDecision.syntaxAllowed c (.«VEC.CONST» v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«VEC.CONST» v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    cases u with
    | VecT vt =>
        cases vt
        refine ⟨vectorWitness, by
          simp [ConstSyntaxDecision.syntaxAllowed,
            ConstArithmeticValidation.arithmeticOps], ?_⟩
        exact ConstVectorDispatch.vec_dispatch_total
          c irt vectorWitness n
    | NumT _ => simp [vectorSeed] at hseed
    | RefT _ => simp [vectorSeed] at hseed
    | BotT => simp [vectorSeed] at hseed
  · rintro ⟨v, _, hcall⟩
    have heffect :=
      (ConstVectorDispatch.vec_literal_effect c irt v _ n n hcall).1
    cases u with
    | VecT vt => cases vt; rfl
    | NumT _ => cases v <;> simp at heffect
    | RefT _ => cases v <;> simp at heffect
    | BotT => cases v <;> simp at heffect

end properties.wasm_module_ok.ConstVectorProduction
