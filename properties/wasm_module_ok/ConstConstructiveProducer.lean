import properties.wasm_module_ok.ConstI31Consumer
import properties.wasm_module_ok.ConstI31Production

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConstructiveProducer

/-- A value can be produced above any existing stack in every local context
reachable from the static origin. The ending context is retained for the next
constructor. -/
def Produces (origin : SpecTec.context) (u : SpecTec.valtype) : Prop :=
  ∀ (current : SpecTec.context),
    ConstStaticAgreement.StaticAgreement origin current →
    ∀ (stack : List SpecTec.valtype) (n : Nat),
      ∃ (xs : List SpecTec.instr) (next : SpecTec.context),
        (∀ i ∈ xs,
          ConstSyntaxDecision.syntaxAllowed origin i = true) ∧
        ConstConstructiveTrace.Trace current (.NoEllipses, stack) xs
          next (.NoEllipses, stack ++ [u]) n n ∧
        ConstStaticAgreement.StaticAgreement origin next

theorem basic_produces
    (origin : SpecTec.context) (u : SpecTec.valtype)
    (hu : u ∈ ConstBasicSeed.basicBase origin) :
    Produces origin u := by
  intro current hstatic stack n
  obtain ⟨i, hsyntax, htrace⟩ :=
    ConstBasicTrace.basic_base_trace_on_stack current stack u n
      (ConstBasicTrace.basic_base_mem_of_static
        origin current hstatic u hu)
  exact ⟨[i], current, by
    intro j hj
    have hj' : j = i := by simpa using hj
    subst j
    rw [ConstStaticAgreement.syntax_allowed origin current hstatic]
    exact hsyntax,
    htrace, hstatic⟩

theorem i31_produces
    (origin : SpecTec.context)
    (hinput : Produces origin (.NumT .I32T)) :
    Produces origin (.RefT (.«% %» .NoNull .I31HT)) := by
  intro current hstatic stack n
  obtain ⟨xs, next, hsyntax, htrace, hnext⟩ :=
    hinput current hstatic stack n
  refine ⟨xs ++ [.«REF.I31»], next, ?_, ?_, hnext⟩
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact hsyntax i hi
    · rw [ConstStaticAgreement.syntax_allowed origin next hnext]
      exact ConstI31Consumer.i31_syntax_allowed next
  · exact ConstI31Consumer.append_i31 stack htrace

theorem i31_produces_from_basic (origin : SpecTec.context)
    (hbase : SpecTec.valtype.NumT .I32T ∈
      ConstBasicSeed.basicBase origin) :
    Produces origin (.RefT (.«% %» .NoNull .I31HT)) :=
  i31_produces origin (basic_produces origin _ hbase)

theorem i31_step_produces
    (origin : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype)
    (hstep : ConstI31Production.i31Step s u = true)
    (hsound : ∀ v ∈ s, Produces origin v) :
    Produces origin u := by
  obtain ⟨hinput, rfl⟩ :=
    (ConstI31Production.i31_step_iff s u).1 hstep
  exact i31_produces origin (hsound _ hinput)

theorem list_produces
    (origin : SpecTec.context) (us : List SpecTec.valtype)
    (hall : ∀ u ∈ us, Produces origin u) :
    ∀ (current : SpecTec.context),
      ConstStaticAgreement.StaticAgreement origin current →
      ∀ (stack : List SpecTec.valtype) (n : Nat),
        ∃ (xs : List SpecTec.instr) (next : SpecTec.context),
          (∀ i ∈ xs,
            ConstSyntaxDecision.syntaxAllowed origin i = true) ∧
          ConstConstructiveTrace.Trace current (.NoEllipses, stack) xs
            next (.NoEllipses, stack ++ us) n n ∧
          ConstStaticAgreement.StaticAgreement origin next := by
  induction us with
  | nil =>
    intro current hstatic stack n
    exact ⟨[], current, by simp,
      by simpa using
        (ConstConstructiveTrace.Trace.nil current
          (.NoEllipses, stack) n), hstatic⟩
  | cons u rest ih =>
    intro current hstatic stack n
    obtain ⟨xs, middle, hxs, hfirst, hmiddle⟩ :=
      hall u (by simp) current hstatic stack n
    obtain ⟨ys, next, hys, hsecond, hnext⟩ :=
      ih (by
        intro v hv
        exact hall v (by simp [hv]))
        middle hmiddle (stack ++ [u]) n
    refine ⟨xs ++ ys, next, ?_, ?_, hnext⟩
    · intro i hi
      simp only [List.mem_append] at hi
      rcases hi with hi | hi
      · exact hxs i hi
      · exact hys i hi
    · simpa only [List.cons_append, List.singleton_append,
        List.nil_append, List.append_assoc] using
        (ConstConstructiveTrace.trace_append hfirst hsecond)

theorem produces_const_of_match
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hproduce : Produces c u)
    (hmatch : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c
        [u] [t]⟩)
      n (.success (.of ())) n) :
    ∃ xs : List SpecTec.instr,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
        n (.success (.of ())) n := by
  obtain ⟨xs, _, hsyntax, htrace, _⟩ :=
    hproduce c (ConstStaticAgreement.refl c) [] n
  have hpop :=
    ConstSingletonFinalPop.singleton_final_pop_of_match_resulttype
      c u t n hmatch
  apply Exists.intro xs
  apply (ConstDecisionTrace.const_ok_decision_trace_iff
    c t xs n n).2
  refine ⟨hsyntax, (.NoEllipses, [u]),
    ([] : List SpecTec.idx), .NoEllipses, n, ?_, hpop⟩
  exact ConstConstructiveTrace.trace_to_instrs
    (by simpa using htrace)

end properties.wasm_module_ok.ConstConstructiveProducer
