import properties.wasm_module_ok.UnpackedFieldDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.StructExplicitFieldsDecision

def structFieldInputs (ys : List SpecTec.fieldtype) :
    List SpecTec.valtype :=
  ys.map UnpackedFieldDecision.unpackedFieldResult

theorem fields_nil_success (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» []⟩)
      n (.success (.of ([] : List SpecTec.valtype))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Instr_ok:struct.new.explicit:iter:1_clauses» []) ())
    n (.success (.of ([] : List SpecTec.valtype))) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:0» [])
    n (.success (.of ([] : List SpecTec.valtype))) n
  exact SpecTecExecution.Eval.pure []

theorem fields_cons_success_iff
    (ft : SpecTec.fieldtype) (ys : List SpecTec.fieldtype)
    (result : List SpecTec.valtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» (ft :: ys)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (t : SpecTec.valtype) (rest : List SpecTec.valtype)
      (middle : Nat),
      result = t :: rest ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.valtype,
          SpecTec.SpecTecCall.«$unpacked_field_type» ft⟩)
        n (.success (.of t)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨List SpecTec.valtype,
          SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
        middle (.success (.of rest)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:0» (ft :: ys))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1»
              (ft :: ys)] ()))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of result)) finalSupply at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse
            (SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1» (ft :: ys))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1» at hsecond
          cases hsecond with
          | bind_success hunpack htail =>
            rename_i middle t
            cases htail with
            | bind_success hrest hpure =>
              rename_i rest
              cases hpure with
              | pure => exact ⟨t, rest, middle, rfl, hunpack, hrest⟩
        | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨t, rest, middle, rfl, hunpack, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Instr_ok:struct.new.explicit:iter:1_clauses» (ft :: ys)) ())
      n (.success (.of (t :: rest))) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:0» (ft :: ys))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1» (ft :: ys))
        n (.success (.of (t :: rest))) finalSupply
      unfold SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1»
      apply SpecTecExecution.Eval.bind_success hunpack
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure (t :: rest)

theorem fields_success_iff_inputs
    (ys : List SpecTec.fieldtype) (result : List SpecTec.valtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
      n (.success (.of result)) finalSupply ↔
    result = structFieldInputs ys ∧ finalSupply = n := by
  induction ys generalizing result n finalSupply with
  | nil =>
    constructor
    · intro h
      have hdet : SpecTecExecution.PrimitiveDeterministic
          SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨hout, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet h (fields_nil_success n)
      cases hout
      exact ⟨rfl, hsupply⟩
    · rintro ⟨hresult, hsupply⟩
      simpa [structFieldInputs, hresult, hsupply] using
        fields_nil_success n
  | cons ft ys ih =>
    constructor
    · intro h
      obtain ⟨t, rest, middle, hresult, hunpack, htail⟩ :=
        (fields_cons_success_iff ft ys result n finalSupply).1 h
      obtain ⟨ht, hm⟩ :=
        (UnpackedFieldDecision.unpacked_field_success_iff_result
          ft t n middle).1 hunpack
      obtain ⟨hrest, hfin⟩ := (ih rest middle finalSupply).1 htail
      rw [hresult, ht, hrest]
      exact ⟨rfl, hfin.trans hm⟩
    · rintro ⟨hresult, hsupply⟩
      have hshape : result =
          UnpackedFieldDecision.unpackedFieldResult ft ::
            structFieldInputs ys := by
        simpa [structFieldInputs] using hresult
      subst result
      subst finalSupply
      apply (fields_cons_success_iff ft ys
        (UnpackedFieldDecision.unpackedFieldResult ft ::
          structFieldInputs ys) n n).2
      exact ⟨UnpackedFieldDecision.unpackedFieldResult ft,
        structFieldInputs ys, n, rfl,
        UnpackedFieldDecision.unpacked_field_total ft n,
        (ih (structFieldInputs ys) n n).2 ⟨rfl, rfl⟩⟩

end properties.wasm_module_ok.StructExplicitFieldsDecision
