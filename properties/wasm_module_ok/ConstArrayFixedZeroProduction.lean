import properties.wasm_module_ok.ConstArrayFixedDispatch
import properties.wasm_module_ok.ArrayTypeDecision
import properties.wasm_module_ok.UnpackedFieldDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedZeroProduction

/-- The zero-length form produces an array reference without stack operands. -/
def arrayFixedZeroSeed (c : SpecTec.context) (u : SpecTec.valtype) : Bool :=
  (List.range c.TYPES.length).any fun x =>
    match c.TYPES[x]?, ArrayTypeDecision.arrayTypeResult c x with
    | some dt, some (.ArrayT _) =>
        decide (u = .RefT (.«% %» .NoNull (.DefHT dt)))
    | _, _ => false

theorem array_fixed_zero_seed_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    arrayFixedZeroSeed c u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype)
        (ft : SpecTec.fieldtype),
        c.TYPES[x]? = some dt ∧
        ArrayTypeDecision.arrayTypeResult c x = some (.ArrayT ft) ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
  simp only [arrayFixedZeroSeed, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, _, hcheck⟩
    cases hget : c.TYPES[x]? with
    | none => simp [hget] at hcheck
    | some dt =>
      cases harray : ArrayTypeDecision.arrayTypeResult c x with
      | none => simp [hget, harray] at hcheck
      | some arr =>
        cases arr with
        | ArrayT ft =>
          refine ⟨x, dt, ft, hget, harray, ?_⟩
          simpa [hget, harray] using hcheck
  · rintro ⟨x, dt, ft, hget, harray, rfl⟩
    refine ⟨x, (List.getElem?_eq_some_iff.mp hget).1, ?_⟩
    simp [hget, harray]

def arrayFixedZeroBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => arrayFixedZeroSeed c u = true)

theorem array_fixed_zero_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ arrayFixedZeroBase c ↔ arrayFixedZeroSeed c u = true := by
  simp only [arrayFixedZeroBase, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hseed
    obtain ⟨x, dt, ft, hget, _, rfl⟩ :=
      (array_fixed_zero_seed_iff c u).1 hseed
    exact ⟨FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget, hseed⟩

theorem array_fixed_zero_seed_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    arrayFixedZeroSeed c u = true ↔
      ∃ (x : SpecTec.typeidx) (dt : SpecTec.deftype),
        c.TYPES[x]? = some dt ∧
        u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
        ConstSyntaxDecision.syntaxAllowed c (.«ARRAY.NEW_FIXED» x 0) = true ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW_FIXED» x 0)⟩)
          n (.success (.of
            (⟨{ INS := (.NoEllipses, []),
                 OUTS := (.NoEllipses, [u]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hseed
    obtain ⟨x, dt, ft, hget, harray, rfl⟩ :=
      (array_fixed_zero_seed_iff c u).1 hseed
    refine ⟨x, dt, hget, rfl, ?_⟩
    apply (ConstArrayFixedDispatch.array_new_fixed_constant_instruction_iff
      c irt x 0 _ n n).2
    refine ⟨ft, UnpackedFieldDecision.unpackedFieldResult ft,
      dt, n, ?_, UnpackedFieldDecision.unpacked_field_total ft n,
      hget, ?_⟩
    · exact (ArrayTypeDecision.array_type_success_iff_result
        c x (.ArrayT ft) n n).2 ⟨harray, rfl⟩
    · rfl
  · rintro ⟨x, dt, hget, _, hsyntax, hcall⟩
    obtain ⟨ft, t, dt', middle, harray, _, hget', hiit⟩ :=
      (ConstArrayFixedDispatch.array_new_fixed_constant_instruction_iff
        c irt x 0 _ n n).1 ⟨hsyntax, hcall⟩
    have hdt : dt' = dt := by
      rw [hget] at hget'
      exact Option.some.inj hget'.symm
    subst dt'
    have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
      have hout := congrArg
        (fun iit : SpecTec.inferinstrtype => iit.1.OUTS.2) hiit
      simpa using hout
    exact (array_fixed_zero_seed_iff c u).2
      ⟨x, dt, ft, hget,
        (ArrayTypeDecision.array_type_success_iff_result
          c x (.ArrayT ft) n middle).1 harray |>.1, hu⟩

end properties.wasm_module_ok.ConstArrayFixedZeroProduction
