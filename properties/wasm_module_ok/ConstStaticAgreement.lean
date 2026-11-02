import properties.wasm_module_ok.ConstClosureStatic
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStaticAgreement

/-- State retained from a module stage while `Instrs_ok` initializes locals
between instructions. -/
structure StaticAgreement (origin current : SpecTec.context) : Prop where
  types : current.TYPES = origin.TYPES
  funcs : current.FUNCS = origin.FUNCS
  globals : current.GLOBALS = origin.GLOBALS
  refs : current.REFS = origin.REFS

theorem refl (c : SpecTec.context) : StaticAgreement c c :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem after_init_locals
    (origin current next : SpecTec.context)
    (indices : List SpecTec.idx) (start finish : Nat)
    (hstatic : StaticAgreement origin current)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» current indices⟩)
      start (.success (.of next)) finish) :
    StaticAgreement origin next := by
  obtain ⟨ht, hf, hg, hr⟩ :=
    LocalInitStatic.init_locals_static_fields current next indices
      start finish hcall
  exact ⟨ht.trans hstatic.types, hf.trans hstatic.funcs,
    hg.trans hstatic.globals, hr.trans hstatic.refs⟩

theorem provenance
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (hprov : CandidateUniverseReady.Provenance origin) :
    CandidateUniverseReady.Provenance current := by
  constructor
  · intro dt hfun
    rw [hstatic.funcs] at hfun
    rw [hstatic.types]
    exact hprov.funcs dt hfun
  · intro gt hglobal
    rw [hstatic.globals] at hglobal
    exact CandidateProvenanceSteps.in_table_val_of_types_eq
      origin current _ hstatic.types (hprov.globals gt hglobal)

theorem ready
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (hready : CandidateTypeReady.Ready origin) :
    CandidateTypeReady.Ready current := by
  exact CandidateProvenanceElemDataFuncs.ready_of_types_eq
    origin current hstatic.types hready

theorem nested_table_ready
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (hready : CandidateNestedReady.nestedTableReady origin = true) :
    CandidateNestedReady.nestedTableReady current = true := by
  rw [ConstTraceNestedReady.nested_table_ready_of_types_eq
    current origin hstatic.types]
  exact hready

theorem in_table_val
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (t : SpecTec.valtype)
    (h : CandidateValMatch.InTableVal origin t) :
    CandidateValMatch.InTableVal current t := by
  exact CandidateProvenanceSteps.in_table_val_of_types_eq
    origin current t hstatic.types h

theorem match_aware_step
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current) :
    ConstMatchAwareClosure.matchAwareStep origin =
      ConstMatchAwareClosure.matchAwareStep current := by
  exact ConstClosureStatic.match_aware_step_of_static_fields
    origin current hstatic.types.symm hstatic.funcs.symm
      hstatic.globals.symm hstatic.refs.symm

theorem closure_iterate
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (round : Nat) :
    FiniteClosure.iterate (ConstMatchAwareClosure.matchAwareStep origin) round =
      FiniteClosure.iterate (ConstMatchAwareClosure.matchAwareStep current) round := by
  rw [match_aware_step origin current hstatic]

theorem syntax_allowed
    (origin current : SpecTec.context)
    (hstatic : StaticAgreement origin current)
    (i : SpecTec.instr) :
    ConstSyntaxDecision.syntaxAllowed origin i =
      ConstSyntaxDecision.syntaxAllowed current i := by
  simp [ConstSyntaxDecision.syntaxAllowed, hstatic.globals.symm]

end properties.wasm_module_ok.ConstStaticAgreement
