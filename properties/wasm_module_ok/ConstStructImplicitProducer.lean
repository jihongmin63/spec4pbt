import properties.wasm_module_ok.ConstConstructiveProducer
import properties.wasm_module_ok.ConstStructImplicitProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructImplicitProducer

theorem seed_of_static
    (origin current : SpecTec.context)
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (u : SpecTec.valtype)
    (hseed : ConstStructImplicitProduction.structImplicitSeed origin u = true) :
    ConstStructImplicitProduction.structImplicitSeed current u = true := by
  simpa [ConstStructImplicitProduction.structImplicitSeed,
    StructTypeDecision.structTypeResult, hstatic.types] using hseed

/-- A defaultable struct is a constant producer above every existing stack. -/
theorem struct_implicit_produces
    (origin : SpecTec.context) (u : SpecTec.valtype)
    (hseed : ConstStructImplicitProduction.structImplicitSeed origin u = true) :
    ConstConstructiveProducer.Produces origin u := by
  intro current hstatic stack n
  obtain ⟨x, _, _, _, hsyntax, hinstr⟩ :=
    (ConstStructImplicitProduction.struct_implicit_seed_iff_instr_effect
      current (.NoEllipses, stack) u n).1
      (seed_of_static origin current hstatic u hseed)
  have hmatch : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype current
        (stack.drop (stack.length - 0)) []⟩)
      n (.success (.of ())) n := by
    simpa using MatchResulttypeValidation.match_resulttype_nil_total current n
  have htrace := ConstConsumerTrace.trace_snoc_of_match
    stack [] u (.«STRUCT.NEW» x .Implicit)
    (ConstConstructiveTrace.Trace.nil current (.NoEllipses, stack) n)
    hinstr (by simp) hmatch
  refine ⟨[.«STRUCT.NEW» x .Implicit], current, ?_, ?_, hstatic⟩
  · intro i hi
    have hi' : i = .«STRUCT.NEW» x .Implicit := by simpa using hi
    subst i
    rw [ConstStaticAgreement.syntax_allowed origin current hstatic]
    exact hsyntax
  · simpa using htrace

theorem struct_implicit_base_produces
    (origin : SpecTec.context) (u : SpecTec.valtype)
    (hbase : u ∈ ConstStructImplicitProduction.structImplicitBase origin) :
    ConstConstructiveProducer.Produces origin u :=
  struct_implicit_produces origin u
    ((ConstStructImplicitProduction.struct_implicit_base_mem_iff
      origin u).1 hbase)

end properties.wasm_module_ok.ConstStructImplicitProducer
