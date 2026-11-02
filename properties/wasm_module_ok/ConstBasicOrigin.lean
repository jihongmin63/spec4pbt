import properties.wasm_module_ok.ConstBasicSeed

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicOrigin

/-- The exact translated nullary instruction effect used by the basic seeds. -/
def EmptyOneEffect (c : SpecTec.context)
    (irt : SpecTec.inferresulttype) (u : SpecTec.valtype)
    (n : Nat) (i : SpecTec.instr) : Prop :=
  ConstSyntaxDecision.syntaxAllowed c i = true ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [u]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n

/-- A disjunction of the five instruction forms in the four basic seed families. -/
def BasicOrigin (c : SpecTec.context)
    (irt : SpecTec.inferresulttype) (u : SpecTec.valtype)
    (n : Nat) : Prop :=
  ((((∃ v : SpecTec.num_, EmptyOneEffect c irt u n (.CONST v)) ∨
   (∃ v : SpecTec.vec_, EmptyOneEffect c irt u n (.«VEC.CONST» v))) ∨
  (∃ ht : SpecTec.heaptype,
    u = .RefT (.«% %» .Null ht) ∧
      EmptyOneEffect c irt u n (.«REF.NULL» ht))) ∨
  (∃ (x : SpecTec.funcidx) (dt : SpecTec.deftype),
    c.FUNCS[x]? = some dt ∧
      u = .RefT (.«% %» .NoNull (.DefHT dt)) ∧
      EmptyOneEffect c irt u n (.«REF.FUNC» x))) ∨
  (∃ (x : SpecTec.globalidx) (t : SpecTec.valtype),
    c.GLOBALS[x]? = some (.GlobalT .Cons t) ∧
      u = t ∧ EmptyOneEffect c irt u n (.«GLOBAL.GET» x))

theorem basic_base_iff_origin
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (n : Nat) :
    u ∈ ConstBasicSeed.basicBase c ↔ BasicOrigin c irt u n := by
  rw [ConstBasicSeed.basic_base_mem_iff]
  simp only [ConstBasicSeed.basicSeed, Bool.or_eq_true]
  rw [ConstLiteralProduction.literal_seed_iff_instr_effect c irt u n,
    ConstRefNullProduction.ref_null_seed_iff_instr_effect c irt u n,
    ConstRefFuncProduction.ref_func_seed_iff_instr_effect c irt u n,
    ConstGlobalGetProduction.global_get_seed_iff_instr_effect c irt u n]
  rfl

end properties.wasm_module_ok.ConstBasicOrigin
