import properties.wasm_module_ok.ConstructiveBodyCatches
import properties.wasm_module_ok.ConstructiveBodyControlProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTryTable
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyBlocktypes
open ConstructiveBodyCatches ConstructiveConstTableCore

theorem handlers_total (c : context) (outputs : List valtype) (xs : List (Handler c)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.«Instr_ok:try_table:iter:0» c outputs (xs.map Subtype.val)⟩)
      n (.success (.of ())) n := by
  induction xs with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:try_table:iter:0_clauses» c outputs []) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure ()
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:try_table:iter:0_clauses» c outputs (x.val::xs.map Subtype.val)) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_unmatch SpecTecExecution.Eval.unmatch
    apply SpecTecExecution.firstSuccess_cons_success
    apply SpecTecExecution.Eval.bind_success (x.property outputs n)
    apply SpecTecExecution.Eval.bind_success ih
    exact SpecTecExecution.Eval.pure ()

theorem try_table (c : context) (stack : inferresulttype) (sig : Signature c)
    (handlers : List (Handler c)) (code : ConstructiveBodyControlProductions.Body
      {c with LABELS:=sig.outputs::c.LABELS} sig.inputs sig.outputs) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack
        (.TRY_TABLE sig.raw (handlers.map Subtype.val) code.val)⟩)
      n (.success (.of (ConstructiveBodyControl.effect sig.inputs sig.outputs))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.TRY_TABLE sig.raw (handlers.map Subtype.val) code.val)
    24 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:24» c stack (.TRY_TABLE sig.raw (handlers.map Subtype.val) code.val)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:24»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.valid n)
  apply SpecTecExecution.Eval.bind_success (handlers_total c sig.outputs handlers n)
  apply SpecTecExecution.Eval.bind_success (code.property n)
  exact SpecTecExecution.Eval.pure _

def controls (c : context) (stack : inferresulttype) (env : Env c) (child : ConstructiveBodyControlProductions.Builder) :
    List (Production c stack) :=
  (signatures c).map fun (sig : Signature c) =>
    let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal c t := fun t ht =>
      ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_left _ ht)
    let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal c t := fun t ht =>
      ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_right _ ht)
    let blockC : context := {c with LABELS:=sig.outputs::c.LABELS}
    let blockGen := child blockC (env.pushLabel sig.outputs ho) sig.inputs sig.outputs
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c blockC t rfl (hi t ht))
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c blockC t rfl (ho t ht))
    ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,sig.inputs) (.NoEllipses,sig.outputs) hi ho
      ((lists c env).bind fun catches => blockGen.map fun code =>
        ⟨.TRY_TABLE sig.raw (catches.map Subtype.val) code.val,try_table c stack sig catches code⟩)

#print axioms try_table
#print axioms controls
end properties.wasm_module_ok.ConstructiveBodyTryTable
