import properties.wasm_module_ok.ConstStructImplicitDispatch
import properties.wasm_module_ok.StructTypeDecision
import properties.wasm_module_ok.StructImplicitFieldsDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructImplicitProduction

/-- A struct with defaultable fields can be produced without stack operands. -/
def structImplicitSeed (c : SpecTec.context) (u : SpecTec.valtype) : Bool :=
  (List.range c.TYPES.length).any fun x =>
    match c.TYPES[x]?, StructTypeDecision.structTypeResult c x with
    | some dt, some (.StructT ys) =>
        StructImplicitFieldsDecision.structFieldsDefaultable ys &&
          decide (u = .RefT (.«% %» .NoNull (.DefHT dt)))
    | _, _ => false

theorem struct_implicit_seed_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    structImplicitSeed c u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype)
        (ys : List SpecTec.fieldtype),
        c.TYPES[x]? = some dt ∧
        StructTypeDecision.structTypeResult c x = some (.StructT ys) ∧
        StructImplicitFieldsDecision.structFieldsDefaultable ys = true ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
  simp only [structImplicitSeed, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, _, hcheck⟩
    cases hget : c.TYPES[x]? with
    | none => simp [hget] at hcheck
    | some dt =>
      cases hstruct : StructTypeDecision.structTypeResult c x with
      | none => simp [hget, hstruct] at hcheck
      | some strct =>
        cases strct with
        | StructT ys =>
          have hparts :
              StructImplicitFieldsDecision.structFieldsDefaultable ys = true ∧
                decide (u = .RefT (.«% %» .NoNull (.DefHT dt))) = true := by
            simpa [hget, hstruct] using hcheck
          exact ⟨x, dt, ys, hget, hstruct, hparts.1,
            by simpa only [decide_eq_true_eq] using hparts.2⟩
  · rintro ⟨x, dt, ys, hget, hstruct, hfields, rfl⟩
    refine ⟨x, (List.getElem?_eq_some_iff.mp hget).1, ?_⟩
    simp [hget, hstruct, hfields]

def structImplicitBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => structImplicitSeed c u = true)

theorem struct_implicit_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ structImplicitBase c ↔ structImplicitSeed c u = true := by
  simp only [structImplicitBase, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hseed
    obtain ⟨x, dt, ys, hget, _, _, rfl⟩ :=
      (struct_implicit_seed_iff c u).1 hseed
    exact ⟨FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget, hseed⟩

theorem struct_implicit_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    structImplicitSeed c u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype),
        c.TYPES[x]? = some dt ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
        ConstSyntaxDecision.syntaxAllowed c (.«STRUCT.NEW» x .Implicit) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«STRUCT.NEW» x .Implicit)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    obtain ⟨x, dt, ys, hget, hstruct, hfields, rfl⟩ :=
      (struct_implicit_seed_iff c u).1 hseed
    refine ⟨x, dt, hget, rfl, ?_⟩
    apply (ConstStructImplicitDispatch.struct_new_implicit_constant_instruction_iff
      c irt x _ n n).2
    refine ⟨ys, dt, n, ?_, ?_, hget, rfl⟩
    · exact (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) n n).2 ⟨hstruct, rfl⟩
    · exact (StructImplicitFieldsDecision.fields_success_iff_defaultable
        ys n n).2 ⟨hfields, rfl⟩
  · rintro ⟨x, dt, hget, _, hsyntax, hcall⟩
    obtain ⟨ys, dt', middle, hstruct, hfields, hget', hiit⟩ :=
      (ConstStructImplicitDispatch.struct_new_implicit_constant_instruction_iff
        c irt x _ n n).1 ⟨hsyntax, hcall⟩
    have hdt : dt' = dt := by
      rw [hget] at hget'
      exact Option.some.inj hget'.symm
    subst dt'
    have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
      have hout := congrArg
        (fun iit : SpecTec.inferinstrtype => iit.1.OUTS.2) hiit
      simpa using hout
    obtain ⟨hstructResult, hmiddle⟩ :=
      (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) n middle).1 hstruct
    obtain ⟨hfieldsResult, _⟩ :=
      (StructImplicitFieldsDecision.fields_success_iff_defaultable
        ys middle n).1 hfields
    exact (struct_implicit_seed_iff c u).2
      ⟨x, dt, ys, hget, hstructResult, hfieldsResult, hu⟩

end properties.wasm_module_ok.ConstStructImplicitProduction
