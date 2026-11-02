import properties.wasm_module_ok.ConstructiveBodyRoute
import properties.wasm_module_ok.ConstructiveBodyBlocktypes
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyControl
open SpecTec properties.wasm_module_ok ConstructiveBodyBlocktypes

def effect (ins outs : List valtype) (locals : List Nat := []) : inferinstrtype :=
  (⟨(.NoEllipses,ins),(.NoEllipses,outs)⟩,locals)

theorem block (c : context) (stack : inferresulttype) (sig : Signature c)
    (body : List instr) (n : Nat)
    (hb : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) body⟩) n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BLOCK sig.raw body)⟩)
      n (.success (.of (effect sig.inputs sig.outputs))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BLOCK sig.raw body) 5 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:5» c stack (.BLOCK sig.raw body)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:5»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.valid n)
  apply SpecTecExecution.Eval.bind_success hb
  exact SpecTecExecution.Eval.pure _

theorem loop (c : context) (stack : inferresulttype) (sig : Signature c)
    (body : List instr) (n : Nat)
    (hb : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Block_ok {c with LABELS:=sig.inputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) body⟩) n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.LOOP sig.raw body)⟩)
      n (.success (.of (effect sig.inputs sig.outputs))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.LOOP sig.raw body) 6 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:6» c stack (.LOOP sig.raw body)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:6»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.valid n)
  apply SpecTecExecution.Eval.bind_success hb
  exact SpecTecExecution.Eval.pure _

theorem ifElse (c : context) (stack : inferresulttype) (sig : Signature c)
    (yes no : List instr) (n : Nat)
    (hy : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) yes⟩) n (.success (.of ())) n)
    (hn : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Block_ok {c with LABELS:=sig.outputs::c.LABELS}
        (.InstrT sig.inputs sig.outputs []) no⟩) n (.success (.of ())) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«IF % % ELSE %» sig.raw yes no)⟩)
      n (.success (.of (effect (sig.inputs++[.NumT .I32T]) sig.outputs))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«IF % % ELSE %» sig.raw yes no) 7 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:7» c stack (.«IF % % ELSE %» sig.raw yes no)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:7»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (sig.valid n)
  apply SpecTecExecution.Eval.bind_success hy
  apply SpecTecExecution.Eval.bind_success hn
  exact SpecTecExecution.Eval.pure _

#print axioms block
#print axioms loop
#print axioms ifElse
end properties.wasm_module_ok.ConstructiveBodyControl
