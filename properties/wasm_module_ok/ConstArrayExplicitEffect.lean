import properties.wasm_module_ok.ConstArrayImplicitEffect
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayExplicitEffect

theorem array_new_explicit_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (yt : SpecTec.fieldtype)
    (t : SpecTec.valtype) (dt : SpecTec.deftype)
    (start middle fin : Nat)
    (harray : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$array_type» c x⟩)
      start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle)
    (hunpack : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$unpacked_field_type» yt⟩)
      middle (.success (.of t)) fin)
    (hget : c.TYPES[x]? = some dt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:64» c irt (.«ARRAY.NEW» x .Explicit))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, [t, .NumT .I32T]),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) fin := by
  unfold SpecTec.«Instr_ok:clause:64»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success harray
  apply SpecTecExecution.Eval.bind_success hunpack
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  rw [hget]
  exact SpecTecExecution.Eval.pure _

theorem array_new_explicit_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:64» c irt (.«ARRAY.NEW» x .Explicit))
      start (.success (.of iit)) fin) :
    ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, [t, .NumT .I32T]),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) finalSupply ∧
      c.TYPES[x]? = some dt := by
    unfold SpecTec.«Instr_ok:clause:64» at h
    cases h with
    | bind_success hguard htail =>
      cases hguard
      cases htail with
      | bind_success hguard htail =>
        cases hguard
        cases htail with
        | bind_success harray htail =>
          rename_i aval
          cases aval with
          | ArrayT yt =>
            cases htail with
            | bind_success hunpack htail =>
              cases htail with
              | bind_success _ htail =>
                cases hget : c.TYPES[x]? with
                | none =>
                  rw [hget] at htail
                  cases htail
                | some dt =>
                  exact ⟨yt, _, dt, _, _, harray, hunpack, rfl⟩
  obtain ⟨yt, t, dt, middle, finalSupply,
    harray, hunpack, hget⟩ := hparts
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (array_new_explicit_clause_total c irt x yt t dt
        start middle finalSupply harray hunpack hget)
  cases hout
  cases hsupply
  exact ⟨yt, t, dt, middle, harray, hunpack, hget, rfl⟩

theorem array_new_explicit_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:64» c irt (.«ARRAY.NEW» x .Explicit))
      start (.success (.of iit)) fin ↔
    ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, [t, .NumT .I32T]),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact array_new_explicit_clause_exact c irt x iit start fin
  · rintro ⟨yt, t, dt, middle, harray, hunpack, hget, hiit⟩
    subst iit
    exact array_new_explicit_clause_total c irt x yt t dt
      start middle fin harray hunpack hget

end properties.wasm_module_ok.ConstArrayExplicitEffect
