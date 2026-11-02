import properties.wasm_module_ok.UnpackedFieldDecision
import properties.wasm_module_ok.DefaultableValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.StructImplicitFieldsDecision

def structFieldsDefaultable (ys : List SpecTec.fieldtype) : Bool :=
  ys.all fun ft =>
    DefaultableValidation.defaultable
      (UnpackedFieldDecision.unpackedFieldResult ft)

theorem fields_nil_success (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Instr_ok:struct.new.implicit:iter:1_clauses» []))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:0» [])
    n (.success (.of ())) n
  exact SpecTecExecution.Eval.pure ()

theorem fields_cons_success_iff
    (ft : SpecTec.fieldtype) (ys : List SpecTec.fieldtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» (ft :: ys)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (t : SpecTec.valtype) (middle after : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» ft⟩)
        n (.success (.of t)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$defaultable» t⟩)
        middle (.success (.of true)) after ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
        after (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse
          (SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:0» (ft :: ys))
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1»
              (ft :: ys)]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.Body
          (.unmatch) n (.success (.of ())) finalSupply at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse
            (SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1» (ft :: ys))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1» at hsecond
          cases hsecond with
          | bind_success hunpack htail =>
            rename_i middle t
            cases htail with
            | bind_success hdefault htail =>
              rename_i after b
              cases htail with
              | bind_success hguard htail =>
                cases hguard with
                | guard_true hb =>
                  cases b with
                  | false => simp at hb
                  | true =>
                    cases htail with
                    | bind_success hrest hpure =>
                      cases hpure with
                      | pure => exact ⟨t, middle, after, hunpack, hdefault, hrest⟩
        | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨t, middle, after, hunpack, hdefault, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Instr_ok:struct.new.implicit:iter:1_clauses» (ft :: ys)))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:0» (ft :: ys))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1» (ft :: ys))
        n (.success (.of ())) finalSupply
      unfold SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1»
      apply SpecTecExecution.Eval.bind_success hunpack
      apply SpecTecExecution.Eval.bind_success hdefault
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

theorem fields_success_iff_defaultable
    (ys : List SpecTec.fieldtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
      n (.success (.of ())) finalSupply ↔
    structFieldsDefaultable ys = true ∧ finalSupply = n := by
  induction ys generalizing n finalSupply with
  | nil =>
    constructor
    · intro h
      obtain ⟨_, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic h (fields_nil_success n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, hsupply⟩
      simpa only [hsupply] using fields_nil_success n
  | cons ft ys ih =>
    constructor
    · intro h
      obtain ⟨t, middle, after, hunpack, hdefault, hrest⟩ :=
        (fields_cons_success_iff ft ys n finalSupply).1 h
      obtain ⟨ht, hm⟩ :=
        (UnpackedFieldDecision.unpacked_field_success_iff_result
          ft t n middle).1 hunpack
      obtain ⟨hb, ha⟩ :=
        (DefaultableValidation.defaultable_success_iff
          t true middle after).1 hdefault
      obtain ⟨hys, hfin⟩ := (ih after finalSupply).1 hrest
      have hhead : DefaultableValidation.defaultable
          (UnpackedFieldDecision.unpackedFieldResult ft) = true := by
        rw [← ht]
        exact hb.symm
      have hall : structFieldsDefaultable (ft :: ys) = true := by
        change (DefaultableValidation.defaultable
          (UnpackedFieldDecision.unpackedFieldResult ft) &&
          structFieldsDefaultable ys) = true
        simp [hhead, hys]
      exact ⟨hall, hfin.trans (ha.trans hm)⟩
    · rintro ⟨hall, hfin⟩
      have hparts :
          DefaultableValidation.defaultable
              (UnpackedFieldDecision.unpackedFieldResult ft) = true ∧
            structFieldsDefaultable ys = true := by
        simpa [structFieldsDefaultable] using hall
      obtain ⟨hhead, htail⟩ := hparts
      subst finalSupply
      apply (fields_cons_success_iff ft ys n n).2
      refine ⟨UnpackedFieldDecision.unpackedFieldResult ft,
        n, n, UnpackedFieldDecision.unpacked_field_total ft n, ?_, ?_⟩
      · simpa [hhead] using
          (DefaultableValidation.defaultable_total
            (UnpackedFieldDecision.unpackedFieldResult ft) n)
      · exact (ih n n).2 ⟨htail, rfl⟩

end properties.wasm_module_ok.StructImplicitFieldsDecision
