import properties.wasm_module_ok.TableDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.AddrNumtypeDecision

def numtypeOfAddrtype : SpecTec.addrtype → SpecTec.numtype
  | .I32AT => .I32T
  | .I64AT => .I64T

theorem numtype_of_addrtype_total
    (addr : SpecTec.addrtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$numtype_of_addrtype» addr⟩)
      n (.success (.of (numtypeOfAddrtype addr))) n := by
  cases addr with
  | I32AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$numtype_of_addrtype_clauses» .I32AT) ())
      n (.success (.of SpecTec.numtype.I32T)) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$numtype_of_addrtype:clause:0» .I32AT)
      n (.success (.of SpecTec.numtype.I32T)) n
    unfold SpecTec.«$numtype_of_addrtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by decide)
    · exact SpecTecExecution.Eval.pure _
  | I64AT =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$numtype_of_addrtype_clauses» .I64AT) ())
      n (.success (.of SpecTec.numtype.I64T)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$numtype_of_addrtype:clause:0» .I64AT)
        n .unmatch n
      unfold SpecTec.«$numtype_of_addrtype:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by decide))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$numtype_of_addrtype:clause:1» .I64AT)
        n (.success (.of SpecTec.numtype.I64T)) n
      unfold SpecTec.«$numtype_of_addrtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by decide)
      · exact SpecTecExecution.Eval.pure _

theorem numtype_of_addrtype_success_iff
    (addr : SpecTec.addrtype) (result : SpecTec.numtype)
    (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.numtype,
        SpecTec.SpecTecCall.«$numtype_of_addrtype» addr⟩)
      start (.success (.of result)) finish ↔
      result = numtypeOfAddrtype addr ∧ finish = start := by
  constructor
  · intro hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    obtain ⟨hresult, hfinish⟩ :=
      SpecTecExecution.eval_deterministic hdet hcall
        (numtype_of_addrtype_total addr start)
    exact ⟨by cases hresult; rfl, hfinish⟩
  · rintro ⟨hresult, hfinish⟩
    subst result
    subst finish
    exact numtype_of_addrtype_total addr start

end properties.wasm_module_ok.AddrNumtypeDecision
