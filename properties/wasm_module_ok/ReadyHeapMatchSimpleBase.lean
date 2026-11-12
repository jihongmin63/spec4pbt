import properties.wasm_module_ok.MatchBaseDefTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyHeapMatchSimpleBase

/-- Exact result of the translated matcher when the source is one of its
eight nonrecursive base heap types. -/
def simpleBaseMatch (source target : SpecTec.heaptype) : Bool :=
  if target = .AnyHT then
    decide (source = .AnyHT ∨ source = .EqHT ∨
      source = .I31HT ∨ source = .StructHT ∨ source = .ArrayHT)
  else if target = .EqHT then
    decide (source = .EqHT ∨ source = .I31HT ∨
      source = .StructHT ∨ source = .ArrayHT)
  else decide (source = target)

theorem simpleBaseMatch_eval
    (dts : List SpecTec.deftype) (source target : SpecTec.heaptype)
    (n : Nat)
    (hsource : source ∈ MatchBaseDefTotal.simpleBaseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_heaptype»
        dts source target⟩)
      n (.success (.of (simpleBaseMatch source target))) n := by
  by_cases hAny : target = .AnyHT
  · subst target
    simp [MatchBaseDefTotal.simpleBaseHeaptypes] at hsource
    rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_any_fallback dts .AnyHT n
          (by simp [MatchBaseDefTotal.anyFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_any_true dts .EqHT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_any_true dts .I31HT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_any_true dts .StructHT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_any_true dts .ArrayHT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_any_fallback dts .FuncHT n
          (by simp [MatchBaseDefTotal.anyFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_any_fallback dts .ExnHT n
          (by simp [MatchBaseDefTotal.anyFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_any_fallback dts .ExternHT n
          (by simp [MatchBaseDefTotal.anyFallbackSources]))
  by_cases hEq : target = .EqHT
  · subst target
    simp [MatchBaseDefTotal.simpleBaseHeaptypes] at hsource
    rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_eq_fallback dts .AnyHT n
          (by simp [MatchBaseDefTotal.eqFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_eq_fallback dts .EqHT n
          (by simp [MatchBaseDefTotal.eqFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_eq_true dts .I31HT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_eq_true dts .StructHT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_core_eq_true dts .ArrayHT n (by simp))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_eq_fallback dts .FuncHT n
          (by simp [MatchBaseDefTotal.eqFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_eq_fallback dts .ExnHT n
          (by simp [MatchBaseDefTotal.eqFallbackSources]))
    · simpa [simpleBaseMatch] using
        (MatchBaseDefTotal.match_simple_eq_fallback dts .ExternHT n
          (by simp [MatchBaseDefTotal.eqFallbackSources]))
  have hAnyGuard :
      SpecTec.«exec:match:heaptype:AnyHT» target = false := by
    cases target <;> simp_all [SpecTec.«exec:match:heaptype:AnyHT»]
  have hEqGuard :
      SpecTec.«exec:match:heaptype:EqHT» target = false := by
    cases target <;> simp_all [SpecTec.«exec:match:heaptype:EqHT»]
  simpa [simpleBaseMatch, hAny, hEq] using
    (MatchBaseDefTotal.match_simple_base_target_eq
      dts source target n hsource hAnyGuard hEqGuard)

end properties.wasm_module_ok.ReadyHeapMatchSimpleBase
