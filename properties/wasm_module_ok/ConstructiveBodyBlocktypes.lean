import properties.wasm_module_ok.ConstructiveBodyDispatch
import properties.wasm_module_ok.FunctionTypeValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBlocktypes
open SpecTec properties.wasm_module_ok

theorem empty_type (c : context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨instrtype,Call.Blocktype_ok c (.ValBlockType none)⟩)
      n (.success (.of (instrtype.InstrT [] [] []))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Blocktype_ok_clauses c (.ValBlockType none)))
    n (.success (.of (instrtype.InstrT [] [] []))) n
  apply SpecTecExecution.tryClauses_cons_success
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem value_type (c : context) (t : valtype) (n : Nat)
    (ht : ValtypeValidation.valtypeValid c t=true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨instrtype,Call.Blocktype_ok c (.ValBlockType (some t))⟩)
      n (.success (.of (instrtype.InstrT [] [t] []))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Blocktype_ok_clauses c (.ValBlockType (some t))))
    n (.success (.of (instrtype.InstrT [] [t] []))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_success
  unfold SpecTec.«Blocktype_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success
    ((ValtypeValidation.valtype_success_iff_valid c t n n).2 ⟨ht,rfl⟩)
  exact SpecTecExecution.Eval.pure _

theorem index_type (c : context) (x : Nat) (ins outs : List valtype) (n : Nat)
    (ht : FunctionTypeValidation.funcTypeResult c x=some (.FuncT ins outs)) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨instrtype,Call.Blocktype_ok c (.VarBlockType x)⟩)
      n (.success (.of (instrtype.InstrT ins outs []))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Blocktype_ok_clauses c (.VarBlockType x)))
    n (.success (.of (instrtype.InstrT ins outs []))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:blocktype:ValBlockType»]))
  apply SpecTecExecution.tryClauses_cons_success
  unfold SpecTec.«Blocktype_ok:clause:2»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success
    ((FunctionTypeValidation.func_type_success_iff_result c x (.FuncT ins outs) n n).2 ⟨ht,rfl⟩)
  exact SpecTecExecution.Eval.pure _

structure Signature (c : context) where
  raw : blocktype
  inputs : List valtype
  outputs : List valtype
  valid : ∀n,SpecTecExecution.Eval SpecTec.Body
    (.call ⟨instrtype,Call.Blocktype_ok c raw⟩)
    n (.success (.of (instrtype.InstrT inputs outputs []))) n

def empty (c : context) : Signature c := ⟨.ValBlockType none,[],[],empty_type c⟩
def value (c : context) (t : valtype) (ht : ValtypeValidation.valtypeValid c t=true) : Signature c :=
  ⟨.ValBlockType (some t),[],[t],fun n => value_type c t n ht⟩
def index (c : context) (x : Nat) (ins outs : List valtype)
    (ht : FunctionTypeValidation.funcTypeResult c x=some (.FuncT ins outs)) : Signature c :=
  ⟨.VarBlockType x,ins,outs,fun n => index_type c x ins outs n ht⟩

/-- Type/index metadata is selected before any body or control AST is emitted. -/
def signatures (c : context) : List (Signature c) :=
  empty c ::
  (FiniteValidTypes.validCandidates c).attach.map (fun t =>
    value c t.val ((FiniteValidTypes.validCandidates_spec c t.val).1 t.property)) ++
  (List.finRange c.TYPES.length).flatMap (fun x =>
    match ht : FunctionTypeValidation.funcTypeResult c x.val with
    | some (.FuncT ins outs) => [index c x.val ins outs ht]
    | none => [])

#print axioms value_type
#print axioms index_type
end properties.wasm_module_ok.ConstructiveBodyBlocktypes
