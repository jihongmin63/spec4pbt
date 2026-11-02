import properties.wasm_module_ok.ConstRefFuncCombined
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefFuncProduction

/-- A safe executable test for the translated free-function set. -/
def hasFuncBool (f : SpecTec.free) (x : SpecTec.funcidx) : Bool :=
  match f.FUNCS with
  | .«`{ % `}» xs => decide (x ∈ xs)

theorem has_func_bool_iff (f : SpecTec.free) (x : SpecTec.funcidx) :
    hasFuncBool f x = true ↔ FreeUnionValidation.HasFunc f x := by
  cases hset : f.FUNCS with
  | «`{ % `}» xs => simp [hasFuncBool, FreeUnionValidation.HasFunc, hset]

/-- An exact finite search for nullary `REF.FUNC` outputs in this context. -/
def refFuncSeed (c : SpecTec.context) (u : SpecTec.valtype) : Bool :=
  (List.range c.FUNCS.length).any fun x =>
    hasFuncBool c.REFS x &&
      match c.FUNCS[x]? with
      | some dt =>
          decide (u = .RefT (.«% %» .NoNull (.DefHT dt)))
      | none => false

def refFuncBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => refFuncSeed c u = true)

theorem ref_func_seed_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    refFuncSeed c u = true ↔
      ∃ (x : SpecTec.funcidx) (dt : SpecTec.deftype),
        c.FUNCS[x]? = some dt ∧
        FreeUnionValidation.HasFunc c.REFS x ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
  simp only [refFuncSeed, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, _, hcheck⟩
    obtain ⟨href, hout⟩ := Bool.and_eq_true_iff.mp hcheck
    cases hget : c.FUNCS[x]? with
    | none => simp [hget] at hout
    | some dt =>
        simp only [hget] at hout
        exact ⟨x, dt, hget, (has_func_bool_iff c.REFS x).1 href,
          by simpa using hout⟩
  · rintro ⟨x, dt, hget, href, rfl⟩
    refine ⟨x, (List.getElem?_eq_some_iff.mp hget).1, ?_⟩
    simp [hget, (has_func_bool_iff c.REFS x).2 href]

theorem ref_func_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ refFuncBase c ↔ refFuncSeed c u = true := by
  simp only [refFuncBase, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hseed
    obtain ⟨x, dt, hget, _, rfl⟩ :=
      (ref_func_seed_iff c u).1 hseed
    exact ⟨FiniteValidTypes.ref_func_output_mem_candidateUniverse
      c x dt hget, hseed⟩

theorem ref_func_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    refFuncSeed c u = true ↔
      ∃ (x : SpecTec.funcidx) (dt : SpecTec.deftype),
        c.FUNCS[x]? = some dt ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
        ConstSyntaxDecision.syntaxAllowed c (.«REF.FUNC» x) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    obtain ⟨x, dt, hget, href, rfl⟩ :=
      (ref_func_seed_iff c u).1 hseed
    refine ⟨x, dt, hget, rfl, ?_⟩
    exact (ConstRefFuncCombined.ref_func_constant_instruction_iff
      c irt x _ n n).2 ⟨dt, hget, href, rfl, rfl⟩
  · rintro ⟨x, dt, hget, rfl, hsyntax, hcall⟩
    obtain ⟨dt', hget', href, hiit, _⟩ :=
      (ConstRefFuncCombined.ref_func_constant_instruction_iff
        c irt x _ n n).1 ⟨hsyntax, hcall⟩
    have hdt : dt' = dt := by
      rw [hget] at hget'
      exact Option.some.inj hget'.symm
    subst dt'
    exact (ref_func_seed_iff c _).2 ⟨x, dt, hget, href, rfl⟩

end properties.wasm_module_ok.ConstRefFuncProduction
