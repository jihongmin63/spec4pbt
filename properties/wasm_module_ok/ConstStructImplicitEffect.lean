import properties.wasm_module_ok.ConstExternConvertDispatch
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructImplicitEffect

theorem struct_new_implicit_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (ys : List SpecTec.fieldtype)
    (dt : SpecTec.deftype) (start middle fin : Nat)
    (hstruct : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.structtype,
        SpecTec.Call.«$struct_type» c x⟩)
      start (.success (.of (SpecTec.structtype.StructT ys))) middle)
    (hfields : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
      middle (.success (.of ())) fin)
    (hget : c.TYPES[x]? = some dt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:60» c irt (.«STRUCT.NEW» x .Implicit))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) fin := by
  unfold SpecTec.«Instr_ok:clause:60»
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

theorem struct_new_implicit_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:60» c irt (.«STRUCT.NEW» x .Implicit))
      start (.success (.of iit)) fin) :
    ∃ ys : List SpecTec.fieldtype, ∃ dt : SpecTec.deftype,
      ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.structtype,
          SpecTec.Call.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
        middle (.success (.of ())) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ ys : List SpecTec.fieldtype, ∃ dt : SpecTec.deftype,
      ∃ middle finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.structtype,
          SpecTec.Call.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
        middle (.success (.of ())) finalSupply ∧
      c.TYPES[x]? = some dt := by
    unfold SpecTec.«Instr_ok:clause:60» at h
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
                  exact ⟨ys, dt, _, _, hstruct, hfields, rfl⟩
  obtain ⟨ys, dt, middle, finalSupply,
    hstruct, hfields, hget⟩ := hparts
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (struct_new_implicit_clause_total c irt x ys dt
        start middle finalSupply hstruct hfields hget)
  cases hout
  cases hsupply
  exact ⟨ys, dt, middle, hstruct, hfields, hget, rfl⟩

theorem struct_new_implicit_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:60» c irt (.«STRUCT.NEW» x .Implicit))
      start (.success (.of iit)) fin ↔
    ∃ ys : List SpecTec.fieldtype, ∃ dt : SpecTec.deftype,
      ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.structtype,
          SpecTec.Call.«$struct_type» c x⟩)
        start (.success (.of (SpecTec.structtype.StructT ys))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Instr_ok:struct.new.implicit:iter:1» ys⟩)
        middle (.success (.of ())) fin ∧
      c.TYPES[x]? = some dt ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact struct_new_implicit_clause_exact c irt x iit start fin
  · rintro ⟨ys, dt, middle, hstruct, hfields, hget, hiit⟩
    subst iit
    exact struct_new_implicit_clause_total c irt x ys dt
      start middle fin hstruct hfields hget

end properties.wasm_module_ok.ConstStructImplicitEffect
