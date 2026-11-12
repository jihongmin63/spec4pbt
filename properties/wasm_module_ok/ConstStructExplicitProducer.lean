import properties.wasm_module_ok.ConstConstructiveOperandSelection
import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstConstructiveMatchStatic
import properties.wasm_module_ok.ConstConsumerTrace
import properties.wasm_module_ok.ConstStructExplicitProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructExplicitProducer

theorem struct_explicit_produces_of_saturation
    (origin : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse origin)
    (hstep : ConstStructExplicitProduction.structExplicitStep origin
      (ConstExtendedMatchSaturation.extendedMatchSaturation origin
        (ConstMatchAwareClosure.sourcesOf origin s)) u = true)
    (hsound : ∀ a ∈ s, ConstConstructiveProducer.Produces origin a)
    (hready : CandidateTypeReady.Ready origin)
    (hsourceTable : ∀ a ∈ s,
      CandidateValMatch.InTableVal origin a)
    (hrequiredTable : ∀ r ∈
      ConstExtendedMatchSaturation.extendedMatchSaturation origin
        (ConstMatchAwareClosure.sourcesOf origin s),
      CandidateValMatch.InTableVal origin r) :
    ConstConstructiveProducer.Produces origin u := by
  obtain ⟨x, dt, ys, hget, hstruct, hu, hinputs⟩ :=
    (ConstStructExplicitProduction.struct_explicit_step_iff
      origin _ u).1 hstep
  subst u
  let required := StructExplicitFieldsDecision.structFieldInputs ys
  obtain ⟨actual, hmem, hpairs⟩ :=
    ConstConstructiveOperandSelection.select_closure_sources
      origin s required hsub hinputs
  intro current hstatic stack n
  obtain ⟨xs, next, hsyntax, htrace, hnext⟩ :=
    ConstConstructiveProducer.list_produces origin actual
      (by
        intro a ha
        exact hsound a (hmem a ha))
      current hstatic stack n
  have hstructNext : StructTypeDecision.structTypeResult next x =
      some (.StructT ys) := by
    simpa [StructTypeDecision.structTypeResult, hnext.types] using hstruct
  have hgetNext : next.TYPES[x]? = some dt := by
    simpa [hnext.types] using hget
  have htype :=
    (StructTypeDecision.struct_type_success_iff_result
      next x (.StructT ys) n n).2 ⟨hstructNext, rfl⟩
  have hfields :=
    (StructExplicitFieldsDecision.fields_success_iff_inputs
      ys required n n).2 ⟨rfl, rfl⟩
  have hpair :=
    (ConstStructExplicitDispatch.struct_new_explicit_constant_instruction_iff
      next (.NoEllipses, stack ++ actual) x
      (⟨{ INS := (.NoEllipses, required),
            OUTS := (.NoEllipses,
              [.RefT (.«% %» .NoNull (.DefHT dt))]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      n n).2
      ⟨ys, required, dt, n, htype, hfields, hgetNext, rfl⟩
  have hmatch :=
    ConstConstructiveMatchStatic.match_resulttype_at_static_context
      origin next actual required n hnext hready hpairs
      (by
        intro a ha
        exact hsourceTable a (hmem a ha))
      (by
        intro r hr
        exact hrequiredTable r (hinputs r hr))
  have htraceNew := ConstConsumerTrace.trace_snoc_after_operands
    stack actual required
    (.RefT (.«% %» .NoNull (.DefHT dt)))
    (.«STRUCT.NEW» x .Explicit)
    htrace hpair.2 hpairs.length_eq.symm hmatch
  refine ⟨xs ++ [.«STRUCT.NEW» x .Explicit], next, ?_, htraceNew,
    hnext⟩
  intro i hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact hsyntax i hi
  · rw [ConstStaticAgreement.syntax_allowed origin next hnext]
    exact hpair.1

end properties.wasm_module_ok.ConstStructExplicitProducer
