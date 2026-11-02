import properties.wasm_module_ok.ConstStructImplicitDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructExplicitEffect

theorem struct_new_explicit_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (ys : List SpecTec.fieldtype)
    (ts : List SpecTec.valtype) (dt : SpecTec.deftype)
    (start middle fin : Nat)
    (hstruct : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.structtype, SpecTec.SpecTecCall.«$struct_type» c x⟩)
      start (.success (.of (SpecTec.structtype.StructT ys))) middle)
    (hfields : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.valtype,
        SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
      middle (.success (.of ts)) fin)
    (hget : c.TYPES[x]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:59» c irt (.«STRUCT.NEW» x .Explicit))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, ts),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) fin := by
  unfold SpecTec.«Instr_ok:clause:59»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success hstruct
  apply SpecTecExecution.Eval.bind_success hfields
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  rw [hget]
  exact SpecTecExecution.Eval.pure _

theorem struct_new_explicit_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:59» c irt (.«STRUCT.NEW» x .Explicit))
      start (.success (.of iit)) fin) :
    ∃ ys : List SpecTec.fieldtype, ∃ ts : List SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.structtype, SpecTec.SpecTecCall.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨List SpecTec.valtype,
          SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
        middle (.success (.of ts)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, ts),
             OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ ys : List SpecTec.fieldtype, ∃ ts : List SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.structtype, SpecTec.SpecTecCall.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨List SpecTec.valtype,
          SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
        middle (.success (.of ts)) finalSupply ∧
      c.TYPES[x]? = some dt := by
    unfold SpecTec.«Instr_ok:clause:59» at h
    cases h with
    | bind_success hguard htail =>
      cases hguard
      cases htail with
      | bind_success hguard htail =>
        cases hguard
        cases htail with
        | bind_success hstruct htail =>
          rename_i st
          cases st with
          | StructT ys =>
            cases htail with
            | bind_success hfields htail =>
              cases htail with
              | bind_success _ htail =>
                cases hget : c.TYPES[x]? with
                | none =>
                  rw [hget] at htail
                  cases htail
                | some dt =>
                  exact ⟨ys, _, dt, _, _, hstruct, hfields, rfl⟩
  obtain ⟨ys, ts, dt, middle, finalSupply,
    hstruct, hfields, hget⟩ := hparts
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request a b hp
    cases hp
  obtain ⟨hout, hsupply⟩ :=
    SpecTecExecution.eval_deterministic hdet h
      (struct_new_explicit_clause_total c irt x ys ts dt
        start middle finalSupply hstruct hfields hget)
  cases hout
  cases hsupply
  exact ⟨ys, ts, dt, middle, hstruct, hfields, hget, rfl⟩

theorem struct_new_explicit_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Instr_ok:clause:59» c irt (.«STRUCT.NEW» x .Explicit))
      start (.success (.of iit)) fin ↔
    ∃ ys : List SpecTec.fieldtype, ∃ ts : List SpecTec.valtype,
      ∃ dt : SpecTec.deftype, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.structtype, SpecTec.SpecTecCall.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨List SpecTec.valtype,
          SpecTec.SpecTecCall.«Instr_ok:struct.new.explicit:iter:1» ys⟩)
        middle (.success (.of ts)) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, ts),
             OUTS := (.NoEllipses, [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact struct_new_explicit_clause_exact c irt x iit start fin
  · rintro ⟨ys, ts, dt, middle, hstruct, hfields, hget, hiit⟩
    subst iit
    exact struct_new_explicit_clause_total c irt x ys ts dt
      start middle fin hstruct hfields hget

end properties.wasm_module_ok.ConstStructExplicitEffect
