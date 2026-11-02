import properties.wasm_module_ok.ModuleRefsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.RefFuncValidation

open properties.wasm_module_ok.FreeUnionValidation

theorem hasFunc_of_in_set_true
    (f : SpecTec.free) (x : SpecTec.funcidx)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$in_set»
        SpecTec.funcidx x f.FUNCS⟩)
      n (.success (.of true)) finalSupply) :
    HasFunc f x := by
  cases hs : f.FUNCS with
  | «`{ % `}» xs =>
    cases hcall with
    | call hbody =>
      rw [hs] at hbody
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$in_set_clauses» SpecTec.funcidx x
            (SpecTec.set.«`{ % `}» xs)))
        n (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$in_set:clause:0» at hclause
        by_cases hx : x ∈ xs
        · simpa only [HasFunc, hs] using hx
        · simp [hx] at hclause
          cases hclause
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem ref_func_clause_success_of_membership
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (dt : SpecTec.deftype) (n : Nat)
    (hlt : x < c.FUNCS.length)
    (hget : c.FUNCS[x]? = some dt)
    (href : HasFunc c.REFS x) :
    ∃ result : SpecTec.inferinstrtype,
      SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
        n (.success (.of result)) n := by
  refine ⟨({
    INS := (.NoEllipses, []),
    OUTS := (.NoEllipses,
      [SpecTec.valtype.RefT
        (SpecTec.reftype.«% %» .NoNull (SpecTec.heaptype.DefHT dt))])
    }, []), ?_⟩
  unfold SpecTec.«Instr_ok:clause:51»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true hlt
  simp only [hget]
  apply SpecTecExecution.Eval.bind_success
    (ModuleRefsValidation.in_set_func_true_of_hasFunc c.REFS x n href)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure _

theorem ref_func_clause_requires_membership
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (result : SpecTec.inferinstrtype)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:51» c irt (.«REF.FUNC» x))
      n (.success (.of result)) finalSupply) :
    x < c.FUNCS.length ∧ HasFunc c.REFS x := by
  unfold SpecTec.«Instr_ok:clause:51» at hcall
  cases hcall with
  | bind_success hmatch htail =>
    cases hmatch with
    | guard_true _ =>
      cases htail with
      | bind_success hbound htail =>
        cases hbound with
        | guard_true hlt =>
          refine ⟨hlt, ?_⟩
          cases hget : c.FUNCS[x]? with
          | none => simp only [hget] at htail; cases htail
          | some dt =>
            simp only [hget] at htail
            cases htail with
            | bind_success hinset htail =>
              cases htail with
              | bind_success hguard _ =>
                cases hguard with
                | guard_true htrue =>
                  subst htrue
                  exact hasFunc_of_in_set_true c.REFS x n _ hinset

end properties.wasm_module_ok.RefFuncValidation
