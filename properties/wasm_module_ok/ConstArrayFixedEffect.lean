import properties.wasm_module_ok.ConstRefFuncCombined
import properties.wasm_module_ok.MakeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedEffect

theorem array_new_fixed_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (yt : SpecTec.fieldtype) (t : SpecTec.valtype)
    (dt : SpecTec.deftype) (start middle finish : Nat)
    (harray : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$array_type» c x⟩)
      start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle)
    (hunpack : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$unpacked_field_type» yt⟩)
      middle (.success (.of t)) finish)
    (hget : c.TYPES[x]? = some dt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x count))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, MakeValidation.makeResult t count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) finish := by
  unfold SpecTec.«Instr_ok:clause:66»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success harray
  apply SpecTecExecution.Eval.bind_success hunpack
  apply SpecTecExecution.Eval.bind_success
    (MakeValidation.make_total SpecTec.valtype t count finish)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  rw [hget]
  exact SpecTecExecution.Eval.pure _

theorem array_new_fixed_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x count))
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
        (⟨{ INS := (.NoEllipses, MakeValidation.makeResult t count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ yt : SpecTec.fieldtype, ∃ t : SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.arraytype,
          SpecTec.Call.«$array_type» c x⟩)
        start (.success (.of (SpecTec.arraytype.ArrayT yt))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.valtype,
          SpecTec.Call.«$unpacked_field_type» yt⟩)
        middle (.success (.of t)) finish ∧
      c.TYPES[x]? = some dt := by
    unfold SpecTec.«Instr_ok:clause:66» at h
    cases h with
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
                        cases htail with
                        | bind_success _ htail =>
                            cases hget : c.TYPES[x]? with
                            | none =>
                                rw [hget] at htail
                                cases htail
                            | some dt =>
                                exact ⟨yt, _, dt, _, _, harray, hunpack, rfl⟩
  obtain ⟨yt, t, dt, middle, finish, harray, hunpack, hget⟩ := hparts
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (array_new_fixed_clause_total c irt x count yt t dt
        start middle finish harray hunpack hget)
  cases hout
  cases hsupply
  exact ⟨yt, t, dt, middle, harray, hunpack, hget, rfl⟩

theorem array_new_fixed_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x count))
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
        (⟨{ INS := (.NoEllipses, MakeValidation.makeResult t count),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact array_new_fixed_clause_exact c irt x count iit start fin
  · rintro ⟨yt, t, dt, middle, harray, hunpack, hget, hiit⟩
    subst iit
    exact array_new_fixed_clause_total c irt x count yt t dt
      start middle fin harray hunpack hget

theorem array_new_fixed_zero_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:66» c irt (.«ARRAY.NEW_FIXED» x 0))
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
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  simpa only [MakeValidation.makeResult] using
    (array_new_fixed_clause_iff c irt x 0 iit start fin)

end properties.wasm_module_ok.ConstArrayFixedEffect
