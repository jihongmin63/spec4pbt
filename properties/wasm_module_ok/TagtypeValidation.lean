import properties.wasm_module_ok.UnrollInterface
import properties.wasm_module_ok.FunctypeProjectionValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.TagtypeValidation

def tagtypeValid : SpecTec.tagtype → Bool
  | .TagT dt =>
      match UnrollInterface.expandResult dt with
      | some (.DefFuncT (.FuncT _ outs)) => outs.isEmpty
      | _ => false

def tagtypeOutcome (tt : SpecTec.tagtype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if tagtypeValid tt then .success (.of ()) else .unmatch

theorem tagtype_total (c : SpecTec.context)
    (tt : SpecTec.tagtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Tagtype_ok c tt⟩)
      n (tagtypeOutcome tt) n := by
  cases tt with
  | TagT dt =>
    cases he : UnrollInterface.expandResult dt with
    | none =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Tagtype_ok_clauses c (.TagT dt)) ())
        n (tagtypeOutcome (.TagT dt)) n
      simp only [tagtypeOutcome, tagtypeValid, he]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Tagtype_ok:clause:0» c (.TagT dt)) n .unmatch n
        unfold SpecTec.«Tagtype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        simpa [UnrollInterface.expandOutcome, he] using
          UnrollInterface.expanddt_total dt n
      · exact SpecTecExecution.firstSuccess_nil () n
    | some st =>
      cases st with
      | DefStructT struct =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Tagtype_ok_clauses c (.TagT dt)) ())
          n (tagtypeOutcome (.TagT dt)) n
        simp only [tagtypeOutcome, tagtypeValid, he]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Tagtype_ok:clause:0» c (.TagT dt)) n .unmatch n
          unfold SpecTec.«Tagtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · simpa [UnrollInterface.expandOutcome, he] using
              UnrollInterface.expanddt_total dt n
          · apply SpecTecExecution.Eval.bind_unmatch
            simpa [FunctypeProjectionValidation.projectionOutcome,
              FunctypeProjectionValidation.functypeProjection] using
              FunctypeProjectionValidation.projection_total
                (.DefStructT struct) n
        · exact SpecTecExecution.firstSuccess_nil () n
      | DefArrayT arr =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Tagtype_ok_clauses c (.TagT dt)) ())
          n (tagtypeOutcome (.TagT dt)) n
        simp only [tagtypeOutcome, tagtypeValid, he]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Tagtype_ok:clause:0» c (.TagT dt)) n .unmatch n
          unfold SpecTec.«Tagtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · simpa [UnrollInterface.expandOutcome, he] using
              UnrollInterface.expanddt_total dt n
          · apply SpecTecExecution.Eval.bind_unmatch
            simpa [FunctypeProjectionValidation.projectionOutcome,
              FunctypeProjectionValidation.functypeProjection] using
              FunctypeProjectionValidation.projection_total
                (.DefArrayT arr) n
        · exact SpecTecExecution.firstSuccess_nil () n
      | DefFuncT ft =>
        cases ft with
        | FuncT ins outs =>
          cases outs with
          | nil =>
            apply SpecTecExecution.Eval.call
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTecExecution.firstSuccess
                (SpecTec.Tagtype_ok_clauses c (.TagT dt)) ())
              n (tagtypeOutcome (.TagT dt)) n
            simp only [tagtypeOutcome, tagtypeValid, he,
              List.isEmpty_nil, ite_true]
            apply SpecTecExecution.firstSuccess_cons_success
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Tagtype_ok:clause:0» c (.TagT dt))
              n (.success (.of ())) n
            unfold SpecTec.«Tagtype_ok:clause:0»
            apply SpecTecExecution.Eval.bind_success
            · simpa [UnrollInterface.expandOutcome, he] using
                UnrollInterface.expanddt_total dt n
            · apply SpecTecExecution.Eval.bind_success
              · exact FunctypeProjectionValidation.projection_total
                  (.DefFuncT (.FuncT ins [])) n
              · apply SpecTecExecution.Eval.bind_success
                · exact SpecTecExecution.Eval.guard_true rfl
                · exact SpecTecExecution.Eval.pure ()
          | cons out outs =>
            apply SpecTecExecution.Eval.call
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTecExecution.firstSuccess
                (SpecTec.Tagtype_ok_clauses c (.TagT dt)) ())
              n (tagtypeOutcome (.TagT dt)) n
            simp only [tagtypeOutcome, tagtypeValid, he,
              List.isEmpty_cons]
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«Tagtype_ok:clause:0» c (.TagT dt))
                n .unmatch n
              unfold SpecTec.«Tagtype_ok:clause:0»
              apply SpecTecExecution.Eval.bind_success
              · simpa [UnrollInterface.expandOutcome, he] using
                  UnrollInterface.expanddt_total dt n
              · apply SpecTecExecution.Eval.bind_success
                · exact FunctypeProjectionValidation.projection_total
                    (.DefFuncT (.FuncT ins (out :: outs))) n
                · apply SpecTecExecution.Eval.bind_unmatch
                  apply SpecTecExecution.Eval.guard_false
                  simp
            · exact SpecTecExecution.firstSuccess_nil () n

theorem tagtype_success_iff_valid (c : SpecTec.context)
    (tt : SpecTec.tagtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Tagtype_ok c tt⟩)
      n (.success (.of ())) finalSupply ↔
    tagtypeValid tt = true ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (tagtype_total c tt n)
    cases hv : tagtypeValid tt with
    | true => exact ⟨rfl, hsupply⟩
    | false => simp [tagtypeOutcome, hv] at hout
  · rintro ⟨hv, rfl⟩
    simpa [tagtypeOutcome, hv] using tagtype_total c tt finalSupply

end properties.wasm_module_ok.TagtypeValidation
