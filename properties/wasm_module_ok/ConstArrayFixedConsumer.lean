import properties.wasm_module_ok.ConstConsumerTrace
import properties.wasm_module_ok.ConstConstructiveMatchStatic
import properties.wasm_module_ok.ConstArrayFixedDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedConsumer

theorem append_array_fixed
    {producerStart matchOrigin current : SpecTec.context}
    {initial : SpecTec.inferresulttype}
    {xs : List SpecTec.instr}
    {start n : Nat}
    (stack actual : List SpecTec.valtype)
    (x count : Nat) (ft : SpecTec.fieldtype) (dt : SpecTec.deftype)
    (htrace : ConstConstructiveTrace.Trace producerStart initial xs current
      (.NoEllipses, stack ++ actual) start n)
    (hstatic : ConstStaticAgreement.StaticAgreement matchOrigin current)
    (harray : ArrayTypeDecision.arrayTypeResult current x =
      some (.ArrayT ft))
    (hget : current.TYPES[x]? = some dt)
    (hready : CandidateTypeReady.Ready matchOrigin)
    (hpairs : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch matchOrigin a r = true)
      actual (MakeValidation.makeResult
        (UnpackedFieldDecision.unpackedFieldResult ft) count))
    (hactual : ∀ a ∈ actual,
      CandidateValMatch.InTableVal matchOrigin a)
    (hrequired : ∀ r ∈ MakeValidation.makeResult
      (UnpackedFieldDecision.unpackedFieldResult ft) count,
      CandidateValMatch.InTableVal matchOrigin r) :
    ConstSyntaxDecision.syntaxAllowed current
      (.«ARRAY.NEW_FIXED» x count) = true ∧
    ConstConstructiveTrace.Trace producerStart initial
      (xs ++ [.«ARRAY.NEW_FIXED» x count]) current
      (.NoEllipses, stack ++
        [.RefT (.«% %» .NoNull (.DefHT dt))]) start n := by
  have htype :=
    (ArrayTypeDecision.array_type_success_iff_result
      current x (.ArrayT ft) n n).2 ⟨harray, rfl⟩
  have hpair :=
    (ConstArrayFixedDispatch.array_new_fixed_constant_instruction_iff
      current (.NoEllipses, stack ++ actual) x count
      (⟨{ INS := (.NoEllipses,
              MakeValidation.makeResult
                (UnpackedFieldDecision.unpackedFieldResult ft) count),
            OUTS := (.NoEllipses,
              [.RefT (.«% %» .NoNull (.DefHT dt))]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype)
      n n).2
      ⟨ft, UnpackedFieldDecision.unpackedFieldResult ft,
        dt, n, htype,
        UnpackedFieldDecision.unpacked_field_total ft n,
        hget, rfl⟩
  have hmatch :=
    ConstConstructiveMatchStatic.match_resulttype_at_static_context
      matchOrigin current actual
      (MakeValidation.makeResult
        (UnpackedFieldDecision.unpackedFieldResult ft) count)
      n hstatic hready hpairs hactual hrequired
  refine ⟨hpair.1, ?_⟩
  exact ConstConsumerTrace.trace_snoc_after_operands
    stack actual
    (MakeValidation.makeResult
      (UnpackedFieldDecision.unpackedFieldResult ft) count)
    (.RefT (.«% %» .NoNull (.DefHT dt)))
    (.«ARRAY.NEW_FIXED» x count)
    htrace hpair.2 hpairs.length_eq.symm hmatch

end properties.wasm_module_ok.ConstArrayFixedConsumer
