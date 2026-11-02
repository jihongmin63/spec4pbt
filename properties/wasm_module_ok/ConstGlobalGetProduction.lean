import properties.wasm_module_ok.ConstGlobalGetCombined
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstGlobalGetProduction

/-- Exact finite search over immutable globals, including `BotT` outputs. -/
def globalGetSeed (c : SpecTec.context) (u : SpecTec.valtype) : Bool :=
  (List.range c.GLOBALS.length).any fun x =>
    match c.GLOBALS[x]? with
    | some (.GlobalT .Cons t) => decide (u = t)
    | _ => false

def globalGetBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => globalGetSeed c u = true)

theorem global_get_seed_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    globalGetSeed c u = true ↔
      ∃ (x : SpecTec.globalidx) (t : SpecTec.valtype),
        c.GLOBALS[x]? = some (.GlobalT .Cons t) ∧ u = t := by
  simp only [globalGetSeed, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, _, hcheck⟩
    cases hget : c.GLOBALS[x]? with
    | none => simp [hget] at hcheck
    | some gt =>
        cases gt with
        | GlobalT m t =>
            cases m with
            | Cons =>
                simp only [hget] at hcheck
                exact ⟨x, t, hget, by simpa using hcheck⟩
            | Var => simp [hget] at hcheck
  · rintro ⟨x, t, hget, rfl⟩
    refine ⟨x, (List.getElem?_eq_some_iff.mp hget).1, ?_⟩
    simp [hget]

theorem global_get_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ globalGetBase c ↔ globalGetSeed c u = true := by
  simp only [globalGetBase, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hseed
    obtain ⟨x, t, hget, rfl⟩ :=
      (global_get_seed_iff c u).1 hseed
    exact ⟨FiniteValidTypes.global_output_mem_candidateUniverse
      c x .Cons u hget, hseed⟩

theorem global_get_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    globalGetSeed c u = true ↔
      ∃ (x : SpecTec.globalidx) (t : SpecTec.valtype),
        c.GLOBALS[x]? = some (.GlobalT .Cons t) ∧
        u = t ∧
        ConstSyntaxDecision.syntaxAllowed c (.«GLOBAL.GET» x) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«GLOBAL.GET» x)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    obtain ⟨x, t, hget, rfl⟩ :=
      (global_get_seed_iff c u).1 hseed
    refine ⟨x, u, hget, rfl, ?_⟩
    exact (ConstGlobalGetCombined.global_get_constant_instruction_iff
      c irt x _ n n).2 ⟨u, hget, rfl, rfl⟩
  · rintro ⟨x, t, hget, rfl, hsyntax, hcall⟩
    obtain ⟨t', hget', hiit, _⟩ :=
      (ConstGlobalGetCombined.global_get_constant_instruction_iff
        c irt x _ n n).1 ⟨hsyntax, hcall⟩
    have ht : t' = u := by
      rw [hget] at hget'
      cases hget'
      rfl
    subst t'
    exact (global_get_seed_iff c _).2 ⟨x, u, hget, rfl⟩

end properties.wasm_module_ok.ConstGlobalGetProduction
