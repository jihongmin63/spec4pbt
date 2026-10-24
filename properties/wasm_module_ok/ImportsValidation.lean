import properties.wasm_module_ok.ImportValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ImportsValidation

def importsResult (c : SpecTec.context) :
    List SpecTec.«import» → Option SpecTec.context
  | [] => some c
  | i :: is =>
      (ImportValidation.importDeclResult c i).bind fun c₁ =>
        importsResult c₁ is

def importsOutcome (c : SpecTec.context) (is : List SpecTec.«import») :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match importsResult c is with
  | none => .unmatch
  | some result => .success (.of result)

theorem imports_total (c : SpecTec.context)
    (is : List SpecTec.«import») (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Imports_ok c is⟩)
      n (importsOutcome c is) n := by
  induction is generalizing c with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Imports_ok_clauses c []) ())
      n (importsOutcome c []) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Imports_ok:clause:0» c []) n .unmatch n
      unfold SpecTec.«Imports_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Imports_ok:clause:1» c [])
        n (importsOutcome c []) n
      unfold SpecTec.«Imports_ok:clause:1»
      simp only [importsOutcome, importsResult]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure c
  | cons i is ih =>
    cases hhead : ImportValidation.importDeclResult c i with
    | none =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Imports_ok_clauses c (i :: is)) ())
        n (importsOutcome c (i :: is)) n
      simp only [importsOutcome, importsResult, hhead, Option.bind_none]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Imports_ok:clause:0» c (i :: is)) n .unmatch n
        unfold SpecTec.«Imports_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          exact ImportValidation.import_ok_none c i n hhead
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Imports_ok:clause:1» c (i :: is)) n .unmatch n
          unfold SpecTec.«Imports_ok:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp
        · exact SpecTecExecution.firstSuccess_nil () n
    | some c₁ =>
      cases htail : importsResult c₁ is with
      | none =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Imports_ok_clauses c (i :: is)) ())
          n (importsOutcome c (i :: is)) n
        simp only [importsOutcome, importsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Imports_ok:clause:0» c (i :: is)) n .unmatch n
          unfold SpecTec.«Imports_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact (ImportValidation.import_ok_success_iff_result
                c i c₁ n n).2 ⟨hhead, rfl⟩
            · apply SpecTecExecution.Eval.bind_unmatch
              simpa [importsOutcome, htail] using ih c₁
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Imports_ok:clause:1» c (i :: is)) n .unmatch n
            unfold SpecTec.«Imports_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp
          · exact SpecTecExecution.firstSuccess_nil () n
      | some result =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Imports_ok_clauses c (i :: is)) ())
          n (importsOutcome c (i :: is)) n
        simp only [importsOutcome, importsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Imports_ok:clause:0» c (i :: is))
          n (.success (.of result)) n
        unfold SpecTec.«Imports_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact (ImportValidation.import_ok_success_iff_result
              c i c₁ n n).2 ⟨hhead, rfl⟩
          · apply SpecTecExecution.Eval.bind_success
            · simpa [importsOutcome, htail] using ih c₁
            · exact SpecTecExecution.Eval.pure result

theorem imports_success_iff_result (c : SpecTec.context)
    (is : List SpecTec.«import») (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Imports_ok c is⟩)
      n (.success (.of result)) finalSupply ↔
    importsResult c is = some result ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (imports_total c is n)
    cases hr : importsResult c is with
    | none => simp [importsOutcome, hr] at hout
    | some result' =>
      simp [importsOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [importsOutcome, hr] using imports_total c is finalSupply

theorem imports_none (c : SpecTec.context)
    (is : List SpecTec.«import») (n : Nat)
    (hr : importsResult c is = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Imports_ok c is⟩)
      n .unmatch n := by
  simpa [importsOutcome, hr] using imports_total c is n

end properties.wasm_module_ok.ImportsValidation
