import properties.wasm_module_ok.LimitsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MemtypeValidation

def memtypeValid : SpecTec.memtype → Bool
  | .MemoryT .I32AT lim => LimitsValidation.limitsValid 65536 lim
  | .MemoryT .I64AT lim => LimitsValidation.limitsValid 281474976710656 lim

def memtypeOutcome (mt : SpecTec.memtype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  if memtypeValid mt then .success (.of ()) else .unmatch

theorem memtype_total (c : SpecTec.context)
    (mt : SpecTec.memtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Memtype_ok c mt⟩)
      n (memtypeOutcome mt) n := by
  cases mt with
  | MemoryT addr lim =>
    cases addr with
    | I32AT =>
      cases hv : LimitsValidation.limitsValid 65536 lim with
      | true =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Memtype_ok_clauses c (.MemoryT .I32AT lim)) ())
          n (memtypeOutcome (.MemoryT .I32AT lim)) n
        simp only [memtypeOutcome, memtypeValid, hv, ite_true]
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Memtype_ok:clause:0» c (.MemoryT .I32AT lim))
          n (.success (.of ())) n
        unfold SpecTec.«Memtype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact (LimitsValidation.limits_success_iff_valid
              c 65536 lim n n).2 ⟨hv, rfl⟩
          · exact SpecTecExecution.Eval.pure ()
      | false =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Memtype_ok_clauses c (.MemoryT .I32AT lim)) ())
          n (memtypeOutcome (.MemoryT .I32AT lim)) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Memtype_ok:clause:0» c (.MemoryT .I32AT lim))
            n .unmatch n
          unfold SpecTec.«Memtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_unmatch
            exact LimitsValidation.limits_invalid_unmatch c 65536 lim n hv
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Memtype_ok:clause:1» c (.MemoryT .I32AT lim))
              n .unmatch n
            unfold SpecTec.«Memtype_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            decide
          · simpa [memtypeOutcome, memtypeValid, hv] using
              (SpecTecExecution.firstSuccess_nil () n)
    | I64AT =>
      cases hv : LimitsValidation.limitsValid 281474976710656 lim with
      | true =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Memtype_ok_clauses c (.MemoryT .I64AT lim)) ())
          n (memtypeOutcome (.MemoryT .I64AT lim)) n
        simp only [memtypeOutcome, memtypeValid, hv, ite_true]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Memtype_ok:clause:0» c (.MemoryT .I64AT lim))
            n .unmatch n
          unfold SpecTec.«Memtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          decide
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Memtype_ok:clause:1» c (.MemoryT .I64AT lim))
            n (.success (.of ())) n
          unfold SpecTec.«Memtype_ok:clause:1»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact (LimitsValidation.limits_success_iff_valid
                c 281474976710656 lim n n).2 ⟨hv, rfl⟩
            · exact SpecTecExecution.Eval.pure ()
      | false =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Memtype_ok_clauses c (.MemoryT .I64AT lim)) ())
          n (memtypeOutcome (.MemoryT .I64AT lim)) n
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Memtype_ok:clause:0» c (.MemoryT .I64AT lim))
            n .unmatch n
          unfold SpecTec.«Memtype_ok:clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          decide
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Memtype_ok:clause:1» c (.MemoryT .I64AT lim))
              n .unmatch n
            unfold SpecTec.«Memtype_ok:clause:1»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · apply SpecTecExecution.Eval.bind_unmatch
              exact LimitsValidation.limits_invalid_unmatch
                c 281474976710656 lim n hv
          · simpa [memtypeOutcome, memtypeValid, hv] using
              (SpecTecExecution.firstSuccess_nil () n)

theorem memtype_success_iff_valid (c : SpecTec.context)
    (mt : SpecTec.memtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Memtype_ok c mt⟩)
      n (.success (.of ())) finalSupply ↔
    memtypeValid mt = true ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (memtype_total c mt n)
    cases hv : memtypeValid mt with
    | true => exact ⟨rfl, hsupply⟩
    | false =>
      simp [memtypeOutcome, hv] at hout
  · rintro ⟨hv, rfl⟩
    simpa [memtypeOutcome, hv] using memtype_total c mt finalSupply

end properties.wasm_module_ok.MemtypeValidation
