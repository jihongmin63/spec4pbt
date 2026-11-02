import properties.wasm_module_ok.ConstStructExplicitDispatch
import properties.wasm_module_ok.StructTypeDecision
import properties.wasm_module_ok.StructExplicitFieldsDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructExplicitProduction

def structExplicitStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) : Bool :=
  (List.range c.TYPES.length).any fun x =>
    match c.TYPES[x]?, StructTypeDecision.structTypeResult c x with
    | some dt, some (.StructT ys) =>
        decide (u = .RefT (.«% %» .NoNull (.DefHT dt))) &&
          (StructExplicitFieldsDecision.structFieldInputs ys).all
            (fun t => decide (t ∈ s))
    | _, _ => false

theorem struct_explicit_step_iff (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    structExplicitStep c s u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype)
        (ys : List SpecTec.fieldtype),
        c.TYPES[x]? = some dt ∧
        StructTypeDecision.structTypeResult c x = some (.StructT ys) ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
        ∀ t ∈ StructExplicitFieldsDecision.structFieldInputs ys, t ∈ s := by
  simp only [structExplicitStep, List.any_eq_true, List.mem_range]
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
              decide (u = .RefT (.«% %» .NoNull (.DefHT dt))) = true ∧
                (StructExplicitFieldsDecision.structFieldInputs ys).all
                  (fun t => decide (t ∈ s)) = true := by
            simpa [hget, hstruct] using hcheck
          refine ⟨x, dt, ys, hget, hstruct,
            by simpa only [decide_eq_true_eq] using hparts.1, ?_⟩
          intro t ht
          exact (decide_eq_true_eq.mp
            ((List.all_eq_true.mp hparts.2) t ht))
  · rintro ⟨x, dt, ys, hget, hstruct, rfl, hinputs⟩
    refine ⟨x, (List.getElem?_eq_some_iff.mp hget).1, ?_⟩
    have hall : (StructExplicitFieldsDecision.structFieldInputs ys).all
        (fun t => decide (t ∈ s)) = true := by
      apply List.all_eq_true.mpr
      intro t ht
      exact decide_eq_true_eq.mpr (hinputs t ht)
    simp [hget, hstruct, hall]

def structExplicitOutputs (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => structExplicitStep c s u = true)

theorem struct_explicit_outputs_mem_iff (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    u ∈ structExplicitOutputs c s ↔ structExplicitStep c s u = true := by
  simp only [structExplicitOutputs, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hstep
    obtain ⟨x, dt, ys, hget, _, rfl, _⟩ :=
      (struct_explicit_step_iff c s u).1 hstep
    exact ⟨FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget, hstep⟩

theorem struct_explicit_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hsub : s ⊆ t)
    (hstep : structExplicitStep c s u = true) :
    structExplicitStep c t u = true := by
  obtain ⟨x, dt, ys, hget, hstruct, hu, hinputs⟩ :=
    (struct_explicit_step_iff c s u).1 hstep
  exact (struct_explicit_step_iff c t u).2
    ⟨x, dt, ys, hget, hstruct, hu, fun v hv => hsub (hinputs v hv)⟩

theorem struct_explicit_outputs_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    structExplicitOutputs c s ⊆ structExplicitOutputs c t := by
  intro u hu
  exact (struct_explicit_outputs_mem_iff c t u).2
    (struct_explicit_step_mono c s t u hsub
      ((struct_explicit_outputs_mem_iff c s u).1 hu))

theorem struct_explicit_step_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) (n : Nat) :
    structExplicitStep c s u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype)
        (ts : List SpecTec.valtype),
        c.TYPES[x]? = some dt ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
        (∀ t ∈ ts, t ∈ s) ∧
        ConstSyntaxDecision.syntaxAllowed c (.«STRUCT.NEW» x .Explicit) = true ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«STRUCT.NEW» x .Explicit)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, ts),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hstep
    obtain ⟨x, dt, ys, hget, hstruct, rfl, hinputs⟩ :=
      (struct_explicit_step_iff c s u).1 hstep
    refine ⟨x, dt, StructExplicitFieldsDecision.structFieldInputs ys,
      hget, rfl, hinputs, ?_⟩
    apply (ConstStructExplicitDispatch.struct_new_explicit_constant_instruction_iff
      c irt x _ n n).2
    refine ⟨ys, StructExplicitFieldsDecision.structFieldInputs ys,
      dt, n, ?_, ?_, hget, rfl⟩
    · exact (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) n n).2 ⟨hstruct, rfl⟩
    · exact (StructExplicitFieldsDecision.fields_success_iff_inputs
        ys (StructExplicitFieldsDecision.structFieldInputs ys) n n).2
        ⟨rfl, rfl⟩
  · rintro ⟨x, dt, ts, hget, _, hinputs, hsyntax, hcall⟩
    obtain ⟨ys, ts', dt', middle, hstruct, hfields, hget', hiit⟩ :=
      (ConstStructExplicitDispatch.struct_new_explicit_constant_instruction_iff
        c irt x _ n n).1 ⟨hsyntax, hcall⟩
    have hdt : dt' = dt := by
      rw [hget] at hget'
      exact Option.some.inj hget'.symm
    subst dt'
    have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
      have hout := congrArg
        (fun iit : SpecTec.inferinstrtype => iit.1.OUTS.2) hiit
      simpa using hout
    have hts : ts = ts' := by
      have hin := congrArg
        (fun iit : SpecTec.inferinstrtype => iit.1.INS.2) hiit
      simpa using hin
    obtain ⟨hstructResult, _⟩ :=
      (StructTypeDecision.struct_type_success_iff_result
        c x (.StructT ys) n middle).1 hstruct
    obtain ⟨hfieldsResult, _⟩ :=
      (StructExplicitFieldsDecision.fields_success_iff_inputs
        ys ts' middle n).1 hfields
    exact (struct_explicit_step_iff c s u).2
      ⟨x, dt, ys, hget, hstructResult, hu,
        by simpa [← hts, ← hfieldsResult] using hinputs⟩

end properties.wasm_module_ok.ConstStructExplicitProduction
