import properties.wasm_module_ok.PeekRefDecision
import properties.wasm_module_ok.ExternopTypeDecision
import properties.wasm_module_ok.ConstExternConvertDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternConvertDecision

def externConvertResult
    (irt : SpecTec.inferresulttype) (op : SpecTec.externop_) :
    Option SpecTec.inferinstrtype :=
  match PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) with
  | none => none
  | some (.«% %» nu _) =>
    let pair := ExternopTypeDecision.typeExternopResult op
    some (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu pair.1)]),
              OUTS := (.NoEllipses, [.RefT (.«% %» nu pair.2)]) },
           ([] : List SpecTec.localidx)⟩)

theorem extern_convert_success_iff_result
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
      start (.success (.of iit)) fin ↔
    externConvertResult irt op = some iit ∧ fin = start := by
  constructor
  · intro h
    obtain ⟨ht1, ht2, nu, ht, middle, htype, hpeek, rfl⟩ :=
      (ConstExternConvertDispatch.extern_convert_dispatch_iff
        c irt op iit start fin).1 h
    obtain ⟨hpair, hmiddle⟩ :=
      (ExternopTypeDecision.type_externop_success_iff_result
        op (ht1, ht2) start middle).1 htype
    obtain ⟨href, hfin⟩ :=
      (PeekRefDecision.peek_ref_success_iff_result
        0 irt (.«% %» nu ht) middle fin).1 hpeek
    have hp1 : ht1 = (ExternopTypeDecision.typeExternopResult op).1 :=
      congrArg Prod.fst hpair
    have hp2 : ht2 = (ExternopTypeDecision.typeExternopResult op).2 :=
      congrArg Prod.snd hpair
    cases hmiddle
    constructor
    · simp [externConvertResult, href, ← hp1, ← hp2]
    · exact hfin
  · rintro ⟨hresult, rfl⟩
    cases href : PeekRefDecision.peekRefResult
        (PeekDecision.peekResult 0 irt) with
    | none =>
      simp [externConvertResult, href] at hresult
    | some rt =>
      cases rt with
      | «% %» nu ht =>
        have hiit : iit =
            (⟨{ INS := (.NoEllipses, [.RefT (.«% %» nu
                       (ExternopTypeDecision.typeExternopResult op).1)]),
                 OUTS := (.NoEllipses, [.RefT (.«% %» nu
                       (ExternopTypeDecision.typeExternopResult op).2)]) },
              ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
          simpa [externConvertResult, href] using hresult.symm
        apply (ConstExternConvertDispatch.extern_convert_dispatch_iff
          c irt op iit fin fin).2
        refine ⟨(ExternopTypeDecision.typeExternopResult op).1,
          (ExternopTypeDecision.typeExternopResult op).2,
          nu, ht, fin, ?_, ?_, hiit⟩
        · exact ExternopTypeDecision.type_externop_total op fin
        · exact PeekRefDecision.peek_ref_total_of_some
            0 irt (.«% %» nu ht) fin href

end properties.wasm_module_ok.ConstExternConvertDecision
