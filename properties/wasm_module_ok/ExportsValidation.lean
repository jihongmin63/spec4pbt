import properties.wasm_module_ok.ExportValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ExportsValidation

def exportsResult (c : SpecTec.context) :
    SpecTec.nameset → List SpecTec.«export» → Option SpecTec.nameset
  | names, [] => some names
  | names, e :: es =>
      (ExportValidation.exportResult c names e).bind fun names₁ =>
        exportsResult c names₁ es

def exportsOutcome (c : SpecTec.context)
    (names : SpecTec.nameset) (es : List SpecTec.«export») :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match exportsResult c names es with
  | none => .unmatch
  | some result => .success (.of result)

theorem exports_total (c : SpecTec.context)
    (names : SpecTec.nameset) (es : List SpecTec.«export»)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.nameset,
        SpecTec.SpecTecCall.Exports_ok c names es⟩)
      n (exportsOutcome c names es) n := by
  induction es generalizing names with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Exports_ok_clauses c names []) ())
      n (exportsOutcome c names []) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Exports_ok:clause:0» c names []) n .unmatch n
      unfold SpecTec.«Exports_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Exports_ok:clause:1» c names [])
        n (exportsOutcome c names []) n
      unfold SpecTec.«Exports_ok:clause:1»
      simp only [exportsOutcome, exportsResult]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure names
  | cons e es ih =>
    cases hhead : ExportValidation.exportResult c names e with
    | none =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Exports_ok_clauses c names (e :: es)) ())
        n (exportsOutcome c names (e :: es)) n
      simp only [exportsOutcome, exportsResult, hhead, Option.bind_none]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Exports_ok:clause:0» c names (e :: es)) n .unmatch n
        unfold SpecTec.«Exports_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          exact ExportValidation.export_ok_none c names e n hhead
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Exports_ok:clause:1» c names (e :: es)) n .unmatch n
          unfold SpecTec.«Exports_ok:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp
        · exact SpecTecExecution.firstSuccess_nil () n
    | some names₁ =>
      cases htail : exportsResult c names₁ es with
      | none =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Exports_ok_clauses c names (e :: es)) ())
          n (exportsOutcome c names (e :: es)) n
        simp only [exportsOutcome, exportsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Exports_ok:clause:0» c names (e :: es)) n .unmatch n
          unfold SpecTec.«Exports_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact (ExportValidation.export_ok_success_iff_result
                c names e names₁ n n).2 ⟨hhead, rfl⟩
            · apply SpecTecExecution.Eval.bind_unmatch
              simpa [exportsOutcome, htail] using ih names₁
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Exports_ok:clause:1» c names (e :: es)) n .unmatch n
            unfold SpecTec.«Exports_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp
          · exact SpecTecExecution.firstSuccess_nil () n
      | some result =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Exports_ok_clauses c names (e :: es)) ())
          n (exportsOutcome c names (e :: es)) n
        simp only [exportsOutcome, exportsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Exports_ok:clause:0» c names (e :: es))
          n (.success (.of result)) n
        unfold SpecTec.«Exports_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact (ExportValidation.export_ok_success_iff_result
              c names e names₁ n n).2 ⟨hhead, rfl⟩
          · apply SpecTecExecution.Eval.bind_success
            · simpa [exportsOutcome, htail] using ih names₁
            · exact SpecTecExecution.Eval.pure result

theorem exports_success_iff_result (c : SpecTec.context)
    (names : SpecTec.nameset) (es : List SpecTec.«export»)
    (result : SpecTec.nameset) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.nameset,
        SpecTec.SpecTecCall.Exports_ok c names es⟩)
      n (.success (.of result)) finalSupply ↔
    exportsResult c names es = some result ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (exports_total c names es n)
    cases hr : exportsResult c names es with
    | none => simp [exportsOutcome, hr] at hout
    | some result' =>
      simp [exportsOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [exportsOutcome, hr] using
      exports_total c names es finalSupply

theorem exports_none (c : SpecTec.context)
    (names : SpecTec.nameset) (es : List SpecTec.«export»)
    (n : Nat) (hr : exportsResult c names es = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.nameset,
        SpecTec.SpecTecCall.Exports_ok c names es⟩)
      n .unmatch n := by
  simpa [exportsOutcome, hr] using exports_total c names es n

end properties.wasm_module_ok.ExportsValidation
