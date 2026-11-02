import properties.wasm_module_ok.ConstArrayFixedConsumer
import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstConstructiveOperandSelection

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedProducer

theorem array_fixed_produces_of_saturation
    (origin : SpecTec.context) (s : Finset SpecTec.valtype)
    (x count : Nat) (ft : SpecTec.fieldtype) (dt : SpecTec.deftype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse origin)
    (harray : ArrayTypeDecision.arrayTypeResult origin x =
      some (.ArrayT ft))
    (hget : origin.TYPES[x]? = some dt)
    (hinputs : ∀ r ∈ MakeValidation.makeResult
      (UnpackedFieldDecision.unpackedFieldResult ft) count,
      r ∈ ConstExtendedMatchSaturation.extendedMatchSaturation origin
        (ConstMatchAwareClosure.sourcesOf origin s))
    (hsound : ∀ a ∈ s, ConstConstructiveProducer.Produces origin a)
    (hready : CandidateTypeReady.Ready origin)
    (hsourceTable : ∀ a ∈ s,
      CandidateValMatch.InTableVal origin a)
    (hrequiredTable : ∀ r ∈ MakeValidation.makeResult
      (UnpackedFieldDecision.unpackedFieldResult ft) count,
      CandidateValMatch.InTableVal origin r) :
    ConstConstructiveProducer.Produces origin
      (.RefT (.«% %» .NoNull (.DefHT dt))) := by
  obtain ⟨actual, hmem, hpairs⟩ :=
    ConstConstructiveOperandSelection.select_closure_sources
      origin s
      (MakeValidation.makeResult
        (UnpackedFieldDecision.unpackedFieldResult ft) count)
      hsub hinputs
  intro current hstatic stack n
  obtain ⟨xs, next, hsyntax, htrace, hnext⟩ :=
    ConstConstructiveProducer.list_produces origin actual
      (by
        intro a ha
        exact hsound a (hmem a ha))
      current hstatic stack n
  have harrayNext : ArrayTypeDecision.arrayTypeResult next x =
      some (.ArrayT ft) := by
    simpa [ArrayTypeDecision.arrayTypeResult, hnext.types] using harray
  have hgetNext : next.TYPES[x]? = some dt := by
    simpa [hnext.types] using hget
  obtain ⟨hsyntaxNew, htraceNew⟩ :=
    ConstArrayFixedConsumer.append_array_fixed stack actual x count ft dt
      htrace hnext harrayNext hgetNext hready hpairs
      (by
        intro a ha
        exact hsourceTable a (hmem a ha))
      hrequiredTable
  refine ⟨xs ++ [.«ARRAY.NEW_FIXED» x count], next, ?_, htraceNew,
    hnext⟩
  intro i hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact hsyntax i hi
  · rw [ConstStaticAgreement.syntax_allowed origin next hnext]
    exact hsyntaxNew

end properties.wasm_module_ok.ConstArrayFixedProducer
