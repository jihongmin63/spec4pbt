import properties.wasm_module_ok.ConstArrayExplicitDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternConvertEffect

theorem extern_convert_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (ht1 ht2 : SpecTec.heaptype)
    (nu : SpecTec.null) (ht : SpecTec.heaptype)
    (start middle fin : Nat)
    (htype : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
        SpecTec.SpecTecCall.«$type_externop» op⟩)
      start (.success (.of (ht1, ht2))) middle)
    (hpeek : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype,
        SpecTec.SpecTecCall.«$peek_ref» 0 irt⟩)
      middle (.success (.of (SpecTec.reftype.«% %» nu ht))) fin) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:77» c irt (.«EXTERN.CONVERT» op))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu ht1)]),
             OUTS := (.NoEllipses, [.RefT (.«% %» nu ht2)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) fin := by
  unfold SpecTec.«Instr_ok:clause:77»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success htype
  apply SpecTecExecution.Eval.bind_success hpeek
  exact SpecTecExecution.Eval.pure _

theorem extern_convert_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:77» c irt (.«EXTERN.CONVERT» op))
      start (.success (.of iit)) fin) :
    ∃ ht1 ht2 : SpecTec.heaptype, ∃ nu : SpecTec.null,
      ∃ ht : SpecTec.heaptype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
          SpecTec.SpecTecCall.«$type_externop» op⟩)
        start (.success (.of (ht1, ht2))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.reftype,
          SpecTec.SpecTecCall.«$peek_ref» 0 irt⟩)
        middle (.success (.of (SpecTec.reftype.«% %» nu ht))) fin ∧
      iit =
        (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu ht1)]),
             OUTS := (.NoEllipses, [.RefT (.«% %» nu ht2)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ ht1 ht2 : SpecTec.heaptype, ∃ nu : SpecTec.null,
      ∃ ht : SpecTec.heaptype, ∃ middle finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
          SpecTec.SpecTecCall.«$type_externop» op⟩)
        start (.success (.of (ht1, ht2))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.reftype,
          SpecTec.SpecTecCall.«$peek_ref» 0 irt⟩)
        middle (.success (.of (SpecTec.reftype.«% %» nu ht))) finalSupply := by
    unfold SpecTec.«Instr_ok:clause:77» at h
    cases h with
    | bind_success hguard htail =>
      cases hguard
      cases htail with
      | bind_success htype htail =>
        rename_i p
        cases p with
        | mk ht1 ht2 =>
          cases htail with
          | bind_success hpeek htail =>
            rename_i rt
            cases rt with
            | «% %» nu ht =>
              exact ⟨ht1, ht2, nu, ht, _, _, htype, hpeek⟩
  obtain ⟨ht1, ht2, nu, ht, middle, finalSupply,
    htype, hpeek⟩ := hparts
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request a b hp
    cases hp
  obtain ⟨hout, hsupply⟩ :=
    SpecTecExecution.eval_deterministic hdet h
      (extern_convert_clause_total c irt op ht1 ht2 nu ht
        start middle finalSupply htype hpeek)
  cases hout
  cases hsupply
  exact ⟨ht1, ht2, nu, ht, middle, htype, hpeek, rfl⟩

theorem extern_convert_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:77» c irt (.«EXTERN.CONVERT» op))
      start (.success (.of iit)) fin ↔
    ∃ ht1 ht2 : SpecTec.heaptype, ∃ nu : SpecTec.null,
      ∃ ht : SpecTec.heaptype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
          SpecTec.SpecTecCall.«$type_externop» op⟩)
        start (.success (.of (ht1, ht2))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.reftype,
          SpecTec.SpecTecCall.«$peek_ref» 0 irt⟩)
        middle (.success (.of (SpecTec.reftype.«% %» nu ht))) fin ∧
      iit =
        (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu ht1)]),
             OUTS := (.NoEllipses, [.RefT (.«% %» nu ht2)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact extern_convert_clause_exact c irt op iit start fin
  · rintro ⟨ht1, ht2, nu, ht, middle, htype, hpeek, hiit⟩
    subst iit
    exact extern_convert_clause_total c irt op ht1 ht2 nu ht
      start middle fin htype hpeek

end properties.wasm_module_ok.ConstExternConvertEffect
