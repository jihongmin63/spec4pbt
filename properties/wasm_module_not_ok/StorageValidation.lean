import properties.wasm_module_not_ok.FunctypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def storagetypeValid (c : SpecTec.context) : SpecTec.storagetype → Bool
  | .ValStorageT t =>
      properties.wasm_module_ok.ValtypeValidation.valtypeValid c t
  | .PackStorageT pt => decide (pt ∈ [SpecTec.packtype.I8, .I16])

theorem storagetype_ok_success_iff_valid (c : SpecTec.context)
    (zt : SpecTec.storagetype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Storagetype_ok c zt⟩)
      start (.success (.of ())) finalSupply ↔
    storagetypeValid c zt = true ∧ finalSupply = start := by
  cases zt with
  | ValStorageT t =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Storagetype_ok:clause:0» c (.ValStorageT t))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«Storagetype_ok:clause:1» c (.ValStorageT t)] ()))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Storagetype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hguard hrest =>
              cases hguard with
              | guard_true _ =>
                cases hrest with
                | bind_success hval hpure =>
                  cases hpure with
                  | pure =>
                    simpa [storagetypeValid] using
                      (properties.wasm_module_ok.ValtypeValidation.valtype_success_iff_valid
                        c t start finalSupply).1 hval
          | orElse_unmatch _ htail =>
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (.orElse (SpecTec.«Storagetype_ok:clause:1» c (.ValStorageT t))
                (fun _ => .unmatch))
              start (.success (.of ())) finalSupply at htail
            cases htail with
            | orElse_success hsecond =>
              unfold SpecTec.«Storagetype_ok:clause:1» at hsecond
              cases hsecond with
              | bind_success hguard _ =>
                cases hguard with
                | guard_true hcond =>
                  simp [SpecTec.«exec:match:storagetype:PackStorageT»] at hcond
            | orElse_unmatch _ hnone => cases hnone
      · rintro ⟨hvalid, rfl⟩
        have hval :=
          (properties.wasm_module_ok.ValtypeValidation.valtype_success_iff_valid
            c t finalSupply finalSupply).2
            ⟨by simpa [storagetypeValid] using hvalid, rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Storagetype_ok_clauses c (.ValStorageT t)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Storagetype_ok:clause:0» c (.ValStorageT t))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Storagetype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
        · apply SpecTecExecution.Eval.bind_success hval
          exact SpecTecExecution.Eval.pure ()
  | PackStorageT pt =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Storagetype_ok:clause:0» c (.PackStorageT pt))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«Storagetype_ok:clause:1» c (.PackStorageT pt)] ()))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Storagetype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond =>
                simp [SpecTec.«exec:match:storagetype:ValStorageT»] at hcond
          | orElse_unmatch _ htail =>
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (.orElse (SpecTec.«Storagetype_ok:clause:1» c (.PackStorageT pt))
                (fun _ => .unmatch))
              start (.success (.of ())) finalSupply at htail
            cases htail with
            | orElse_success hsecond =>
              unfold SpecTec.«Storagetype_ok:clause:1» at hsecond
              cases hsecond with
              | bind_success hguard hrest =>
                cases hguard with
                | guard_true _ =>
                  cases hrest with
                  | bind_success hmember hpure =>
                    cases hpure with
                    | pure =>
                      cases hmember with
                      | guard_true hmem =>
                        exact ⟨by simpa [storagetypeValid] using hmem, rfl⟩
            | orElse_unmatch _ hnone => cases hnone
      · rintro ⟨hvalid, rfl⟩
        have hmem : pt ∈ [SpecTec.packtype.I8, .I16] := by
          simpa [storagetypeValid] using hvalid
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Storagetype_ok_clauses c (.PackStorageT pt)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Storagetype_ok:clause:0» c (.PackStorageT pt))
            finalSupply .unmatch finalSupply
          unfold SpecTec.«Storagetype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Storagetype_ok:clause:1» c (.PackStorageT pt))
            finalSupply (.success (.of ())) finalSupply
          unfold SpecTec.«Storagetype_ok:clause:1»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
          · apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true hmem
            · exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_not_ok.Rejection
