import properties.wasm_module_ok.ConstStructExplicitDispatch
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstNumericBinopEffect

theorem numeric_binop_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (nt : SpecTec.numtype)
    (start fin : Nat)
    (htype : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.numtype,
        SpecTec.Call.«$type_num»
          SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop op⟩)
      start (.success (.of nt)) fin) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:82» c irt (.BINOP op))
      start (.success (.of
        (⟨{ INS := (.NoEllipses, [.NumT nt, .NumT nt]),
             OUTS := (.NoEllipses, [.NumT nt]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) fin := by
  unfold SpecTec.«Instr_ok:clause:82»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success htype
  exact SpecTecExecution.Eval.pure _

theorem numeric_binop_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:82» c irt (.BINOP op))
      start (.success (.of iit)) fin) :
    ∃ nt : SpecTec.numtype,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.numtype,
          SpecTec.Call.«$type_num»
            SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop op⟩)
        start (.success (.of nt)) fin ∧
      iit =
        (⟨{ INS := (.NoEllipses, [.NumT nt, .NumT nt]),
             OUTS := (.NoEllipses, [.NumT nt]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  have hparts : ∃ nt : SpecTec.numtype, ∃ finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.numtype,
          SpecTec.Call.«$type_num»
            SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop op⟩)
        start (.success (.of nt)) finalSupply := by
    unfold SpecTec.«Instr_ok:clause:82» at h
    cases h with
    | bind_success hguard htail =>
      cases hguard
      cases htail with
      | bind_success htype _ =>
        exact ⟨_, _, htype⟩
  obtain ⟨nt, finalSupply, htype⟩ := hparts
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (numeric_binop_clause_total c irt op nt start finalSupply htype)
  cases hout
  cases hsupply
  exact ⟨nt, htype, rfl⟩

theorem numeric_binop_clause_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:82» c irt (.BINOP op))
      start (.success (.of iit)) fin ↔
    ∃ nt : SpecTec.numtype,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.numtype,
          SpecTec.Call.«$type_num»
            SpecTec.ibinop SpecTec.ibinop SpecTec.fbinop SpecTec.fbinop op⟩)
        start (.success (.of nt)) fin ∧
      iit =
        (⟨{ INS := (.NoEllipses, [.NumT nt, .NumT nt]),
             OUTS := (.NoEllipses, [.NumT nt]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) := by
  constructor
  · exact numeric_binop_clause_exact c irt op iit start fin
  · rintro ⟨nt, htype, hiit⟩
    subst iit
    exact numeric_binop_clause_total c irt op nt start fin htype

end properties.wasm_module_ok.ConstNumericBinopEffect
