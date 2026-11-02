import properties.wasm_module_ok.ValidatedTypeSubstitution
import properties.wasm_module_ok.ValidatedUnrolledPredecessors

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypeReady

open properties.wasm_module_not_ok.Rejection

/-- The conditions needed to run the type matcher on a substituted candidate
group. They concern the whole candidate type table, including entries that
have not yet passed `Rectype_ok`. -/
structure Ready (c : SpecTec.context) : Prop where
  substitution : ∀ (p : Nat) (dt : SpecTec.deftype), c.TYPES[p]? = some dt →
    substDeftypeResult dt c.TYPES = some dt
  unrolledPredecessors : ∀ p, p < c.TYPES.length →
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin hts strt) ∧
      ∀ j, j < hts.length →
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          k < p ∧ c.TYPES[k]? = some dtK ∧
          hts[j]? = some (.DefHT dtK)

theorem validated_types_ready
    (c : SpecTec.context)
    (hc : ValidatedTypeChain.ValidatedTypes c) : Ready c := by
  constructor
  · intro p dt hlookup
    have hp : p < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hlookup).choose
    have hcall :=
      ValidatedTypeSubstitution.validated_type_substitution_fixed
        c p 0 dt hc hp hlookup
    have hdet :=
      (subst_deftype_of_deterministic dt c.TYPES 0 0
        (.success (.of dt)) hcall).1
    cases hresult : substDeftypeResult dt c.TYPES with
    | none =>
        simp [optionOutcome, hresult] at hdet
    | some dt' =>
        have heq : dt = dt' := by
          simpa [optionOutcome, hresult] using hdet
        subst dt'
        rfl
  · intro p hp
    exact ValidatedUnrolledPredecessors.validated_type_unrolled_predecessors
      c p hc hp

end properties.wasm_module_ok.CandidateTypeReady
