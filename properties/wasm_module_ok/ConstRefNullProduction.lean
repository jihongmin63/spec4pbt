import properties.wasm_module_ok.ConstRefNullDispatch
import properties.wasm_module_ok.ConstSyntaxDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefNullProduction

def refNullSeed (c : SpecTec.context) : SpecTec.valtype → Bool
  | .RefT (.«% %» .Null ht) => HeaptypeValidation.heaptypeValid c ht
  | _ => false

def refNullBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  ((FiniteValidTypes.heapCandidates c).map
    (fun ht => SpecTec.valtype.RefT (.«% %» .Null ht))).toFinset

theorem ref_null_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ refNullBase c ↔ refNullSeed c u = true := by
  simp only [refNullBase, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨ht, hmem, rfl⟩
    exact (FiniteValidTypes.heapCandidates_spec c ht).1 hmem
  · intro hseed
    cases u with
    | RefT ref =>
        cases ref with
        | «% %» null ht =>
            cases null with
            | Null =>
                exact ⟨ht,
                  (FiniteValidTypes.heapCandidates_spec c ht).2 hseed,
                  rfl⟩
            | NoNull => simp [refNullSeed] at hseed
    | NumT _ => simp [refNullSeed] at hseed
    | VecT _ => simp [refNullSeed] at hseed
    | BotT => simp [refNullSeed] at hseed

theorem ref_null_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    refNullSeed c u = true ↔
      ∃ ht : SpecTec.heaptype,
        u = .RefT (.«% %» .Null ht) ∧
        ConstSyntaxDecision.syntaxAllowed c (.«REF.NULL» ht) = true ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.SpecTecCall.Instr_ok c irt (.«REF.NULL» ht)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    cases u with
    | RefT ref =>
        cases ref with
        | «% %» null ht =>
            cases null with
            | Null =>
                refine ⟨ht, rfl, by
                  simp [ConstSyntaxDecision.syntaxAllowed,
                    ConstArithmeticValidation.arithmeticOps], ?_⟩
                exact (ConstRefNullDispatch.ref_null_dispatch_iff
                  c irt ht _ n n).2 ⟨hseed, rfl, rfl⟩
            | NoNull => simp [refNullSeed] at hseed
    | NumT _ => simp [refNullSeed] at hseed
    | VecT _ => simp [refNullSeed] at hseed
    | BotT => simp [refNullSeed] at hseed
  · rintro ⟨ht, rfl, _, hcall⟩
    exact (ConstRefNullDispatch.ref_null_dispatch_iff
      c irt ht _ n n).1 hcall |>.1

end properties.wasm_module_ok.ConstRefNullProduction
