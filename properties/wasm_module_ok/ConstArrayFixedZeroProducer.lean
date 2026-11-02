import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstArrayFixedZeroProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedZeroProducer

theorem seed_of_static
    (origin current : SpecTec.context)
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (u : SpecTec.valtype)
    (hseed : ConstArrayFixedZeroProduction.arrayFixedZeroSeed origin u = true) :
    ConstArrayFixedZeroProduction.arrayFixedZeroSeed current u = true := by
  simpa [ConstArrayFixedZeroProduction.arrayFixedZeroSeed,
    ArrayTypeDecision.arrayTypeResult, hstatic.types] using hseed

/-- A zero-length array is a constant producer above every existing stack. -/
theorem zero_array_produces
    (origin : SpecTec.context) (u : SpecTec.valtype)
    (hseed : ConstArrayFixedZeroProduction.arrayFixedZeroSeed origin u = true) :
    ConstConstructiveProducer.Produces origin u := by
  intro current hstatic stack n
  obtain ⟨x, dt, _, _, hsyntax, hinstr⟩ :=
    (ConstArrayFixedZeroProduction.array_fixed_zero_seed_iff_instr_effect
      current (.NoEllipses, stack) u n).1
      (seed_of_static origin current hstatic u hseed)
  have hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        (stack.drop (stack.length - 0)) []⟩)
      n (.success (.of ())) n := by
    simpa using MatchResulttypeValidation.match_resulttype_nil_total current n
  have htrace := ConstConsumerTrace.trace_snoc_of_match
    stack [] u (.«ARRAY.NEW_FIXED» x 0)
    (ConstConstructiveTrace.Trace.nil current (.NoEllipses, stack) n)
    hinstr (by simp) hmatch
  refine ⟨[.«ARRAY.NEW_FIXED» x 0], current, ?_, ?_, hstatic⟩
  · intro i hi
    have hi' : i = .«ARRAY.NEW_FIXED» x 0 := by simpa using hi
    subst i
    rw [ConstStaticAgreement.syntax_allowed origin current hstatic]
    exact hsyntax
  · simpa using htrace

theorem zero_array_base_produces
    (origin : SpecTec.context) (u : SpecTec.valtype)
    (hbase : u ∈ ConstArrayFixedZeroProduction.arrayFixedZeroBase origin) :
    ConstConstructiveProducer.Produces origin u :=
  zero_array_produces origin u
    ((ConstArrayFixedZeroProduction.array_fixed_zero_base_mem_iff
      origin u).1 hbase)

end properties.wasm_module_ok.ConstArrayFixedZeroProducer
