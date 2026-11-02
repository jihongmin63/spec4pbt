import properties.wasm_module_not_ok.HeaptypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substReftypeResult (rt : SpecTec.reftype)
    (dts : List SpecTec.deftype) : Option SpecTec.reftype :=
  match rt with
  | .«% %» null ht =>
      (substHeaptypeResult ht dts).map (fun ht' => .«% %» null ht')

theorem subst_reftype_of_total (rt : SpecTec.reftype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype,
        SpecTec.SpecTecCall.«$subst_reftype»
          (List SpecTec.deftype) dts
          SpecTec.SpecTecCall.«$subst_of» rt⟩)
      start (optionOutcome (substReftypeResult rt dts)) start := by
  cases rt with
  | «% %» null ht =>
      cases hresult : substHeaptypeResult ht dts with
      | some ht' =>
          have hheap : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_heaptype»
                  (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» ht⟩)
              start (.success (.of ht')) start := by
            simpa [optionOutcome, hresult] using
              subst_heaptype_of_total ht dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_reftype_clauses»
                (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.«% %» null ht)) ())
            start (optionOutcome
              (substReftypeResult (.«% %» null ht) dts)) start
          simp only [substReftypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_reftype:clause:0»
              (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.«% %» null ht))
            start (.success (.of (SpecTec.reftype.«% %» null ht'))) start
          unfold SpecTec.«$subst_reftype:clause:0»
          apply SpecTecExecution.Eval.bind_success hheap
          simpa [substReftypeResult, optionOutcome, hresult] using
            (SpecTecExecution.Eval.pure
              (SpecTec.reftype.«% %» null ht') (n := start))
      | none =>
          have hheap : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_heaptype»
                  (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» ht⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using
              subst_heaptype_of_total ht dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_reftype_clauses»
                (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.«% %» null ht)) ())
            start (optionOutcome
              (substReftypeResult (.«% %» null ht) dts)) start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_reftype:clause:0»
                (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.«% %» null ht))
              start .unmatch start
            unfold SpecTec.«$subst_reftype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hheap
          · simpa [substReftypeResult, optionOutcome, hresult] using
              (SpecTecExecution.firstSuccess_nil () start)

theorem subst_reftype_of_deterministic (rt : SpecTec.reftype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype,
        SpecTec.SpecTecCall.«$subst_reftype»
          (List SpecTec.deftype) dts
          SpecTec.SpecTecCall.«$subst_of» rt⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substReftypeResult rt dts) ∧
      finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_reftype_of_total rt dts start)

end properties.wasm_module_not_ok.Rejection
