import properties.wasm_module_ok.ConstConstructiveTrace
import properties.wasm_module_ok.ConstNullaryTrace
import properties.wasm_module_ok.PopGeneralValidation
import properties.wasm_module_ok.ConstStaticAgreement

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicTrace

theorem basic_base_trace_singleton
    (c : SpecTec.context) (u : SpecTec.valtype) (n : Nat)
    (hu : u ∈ ConstBasicSeed.basicBase c) :
    ∃ (i : SpecTec.instr) (next : SpecTec.context),
      ConstSyntaxDecision.syntaxAllowed c i = true ∧
      ConstConstructiveTrace.Trace c (.NoEllipses, []) [i]
        next (.NoEllipses, [u]) n n := by
  obtain ⟨i, hsyntax, hinstrs⟩ :=
    ConstNullaryTrace.basic_base_instrs_singleton c u n hu
  obtain ⟨next, htrace⟩ :=
    ConstConstructiveTrace.instrs_to_trace [i] c (.NoEllipses, [])
      (.NoEllipses, [u]) n n hinstrs
  exact ⟨i, next, hsyntax, htrace⟩

theorem pop_empty_from_stack
    (c : SpecTec.context) (stack : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c (.NoEllipses, [])
          (.NoEllipses, stack)⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses, stack))) n := by
  simpa using
    (PopGeneralValidation.pop_noellipses_of_match c [] stack n n
      (by simp) (by simpa using
        MatchResulttypeValidation.match_resulttype_nil_total c n))

theorem basic_base_trace_on_stack
    (c : SpecTec.context) (stack : List SpecTec.valtype)
    (u : SpecTec.valtype) (n : Nat)
    (hu : u ∈ ConstBasicSeed.basicBase c) :
    ∃ i : SpecTec.instr,
      ConstSyntaxDecision.syntaxAllowed c i = true ∧
      ConstConstructiveTrace.Trace c (.NoEllipses, stack) [i]
        c (.NoEllipses, stack ++ [u]) n n := by
  have horigin :=
    (ConstBasicOrigin.basic_base_iff_origin c
      (.NoEllipses, stack) u n).1 hu
  have hmake (i : SpecTec.instr)
      (h : ConstBasicOrigin.EmptyOneEffect c
        (.NoEllipses, stack) u n i) :
      ∃ i : SpecTec.instr,
        ConstSyntaxDecision.syntaxAllowed c i = true ∧
        ConstConstructiveTrace.Trace c (.NoEllipses, stack) [i]
          c (.NoEllipses, stack ++ [u]) n n := by
    refine ⟨i, h.1, ?_⟩
    apply ConstConstructiveTrace.Trace.cons h.2
      (LocalInitValidation.init_locals_nil_total c n)
      (pop_empty_from_stack c stack n)
    · simpa [PushValidation.pushOutcome, PushValidation.pushResult] using
        (PushValidation.push_total c (.NoEllipses, [u])
          (.NoEllipses, stack) n)
    · exact ConstConstructiveTrace.Trace.nil c
        (.NoEllipses, stack ++ [u]) n
  rcases horigin with ((((⟨v, hv⟩ | ⟨v, hv⟩) |
      ⟨ht, _, hv⟩) | ⟨x, dt, _, _, hv⟩) |
      ⟨x, t, _, _, hv⟩)
  · exact hmake (.CONST v) hv
  · exact hmake (.«VEC.CONST» v) hv
  · exact hmake (.«REF.NULL» ht) hv
  · exact hmake (.«REF.FUNC» x) hv
  · exact hmake (.«GLOBAL.GET» x) hv

theorem basic_base_mem_of_static
    (origin current : SpecTec.context)
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (u : SpecTec.valtype)
    (hu : u ∈ ConstBasicSeed.basicBase origin) :
    u ∈ ConstBasicSeed.basicBase current := by
  rw [ConstClosureStatic.basic_base_of_static_fields
    origin current hstatic.types.symm hstatic.funcs.symm
      hstatic.globals.symm hstatic.refs.symm] at hu
  exact hu

theorem basic_list_trace
    (origin current : SpecTec.context)
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (us : List SpecTec.valtype)
    (hall : ∀ u ∈ us, u ∈ ConstBasicSeed.basicBase origin) :
    ∀ (stack : List SpecTec.valtype) (n : Nat),
      ∃ xs : List SpecTec.instr,
        (∀ i ∈ xs,
          ConstSyntaxDecision.syntaxAllowed origin i = true) ∧
        ConstConstructiveTrace.Trace current (.NoEllipses, stack) xs
          current (.NoEllipses, stack ++ us) n n := by
  induction us with
  | nil =>
    intro stack n
    exact ⟨[], by simp,
      by simpa using
        (ConstConstructiveTrace.Trace.nil current
          (.NoEllipses, stack) n)⟩
  | cons u rest ih =>
    intro stack n
    have hu : u ∈ ConstBasicSeed.basicBase origin :=
      hall u (by simp)
    obtain ⟨i, hsyntax, hstep⟩ :=
      basic_base_trace_on_stack current stack u n
        (basic_base_mem_of_static origin current hstatic u hu)
    obtain ⟨ys, hysyntax, htail⟩ :=
      ih (by
        intro v hv
        exact hall v (by simp [hv])) (stack ++ [u]) n
    refine ⟨[i] ++ ys, ?_, ?_⟩
    · intro j hj
      simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with rfl | hj
      · rw [ConstStaticAgreement.syntax_allowed origin current hstatic]
        exact hsyntax
      · exact hysyntax j hj
    · simpa only [List.singleton_append, List.cons_append,
        List.nil_append, List.append_assoc] using
        (ConstConstructiveTrace.trace_append hstep htail)

end properties.wasm_module_ok.ConstBasicTrace
