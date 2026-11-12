import properties.wasm_module_ok.ConstLiteralDispatch
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstNumericProduction

/-- The nullary numeric production in the finite constant-type closure. -/
def numericSeed : SpecTec.valtype → Bool
  | .NumT _ => true
  | _ => false

def numericWitness : SpecTec.numtype → SpecTec.num_
  | .I32T => .I32 0
  | .I64T => .I64 0
  | .F32T => .F32 (.POS .INF)
  | .F64T => .F64 (.POS .INF)

theorem numeric_type_witness (nt : SpecTec.numtype) :
    ConstLiteralEffect.numericType (numericWitness nt) = nt := by
  cases nt <;> rfl

theorem numeric_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    numericSeed u = true ↔
      ∃ v : SpecTec.num_,
        ConstSyntaxDecision.syntaxAllowed c (.CONST v) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.CONST v)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    cases u with
    | NumT nt =>
        refine ⟨numericWitness nt, by
          simp [ConstSyntaxDecision.syntaxAllowed,
            ConstArithmeticValidation.arithmeticOps], ?_⟩
        simpa only [numeric_type_witness] using
          ConstLiteralDispatch.const_dispatch_total
            c irt (numericWitness nt) n
    | VecT _ => simp [numericSeed] at hseed
    | RefT _ => simp [numericSeed] at hseed
    | BotT => simp [numericSeed] at hseed
  · rintro ⟨v, _, hcall⟩
    have heffect :=
      (ConstLiteralDispatch.const_literal_effect c irt v _ n n hcall).1
    cases u with
    | NumT _ => rfl
    | VecT _ => cases v <;> simp [ConstLiteralEffect.numericType] at heffect
    | RefT _ => cases v <;> simp [ConstLiteralEffect.numericType] at heffect
    | BotT => cases v <;> simp [ConstLiteralEffect.numericType] at heffect

end properties.wasm_module_ok.ConstNumericProduction
