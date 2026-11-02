import properties.wasm_module_ok.ConstructiveBodySimpleAtoms
import properties.wasm_module_ok.ConstructiveBodyBlocktypeCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyControlProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyBlocktypes ConstructiveConstTableCore

abbrev Body (c : context) (ins outs : List valtype) :=
  {code : List instr // ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨Unit,SpecTecCall.Block_ok c (.InstrT ins outs []) code⟩)
    n (.success (.of ())) n}

abbrev Builder := (c : context) → Env c → (ins outs : List valtype) →
  (∀t∈ins,CandidateValMatch.InTableVal c t) →
  (∀t∈outs,CandidateValMatch.InTableVal c t) → Audited (Body c ins outs)

def controls (c : context) (stack : inferresulttype) (env : Env c) (child : Builder) :
    List (Production c stack) :=
  (signatures c).flatMap fun (sig : Signature c) =>
    let hi : ∀t∈sig.inputs,CandidateValMatch.InTableVal c t := fun t ht =>
      ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_left _ ht)
    let ho : ∀t∈sig.outputs,CandidateValMatch.InTableVal c t := fun t ht =>
      ConstructiveBodyBlocktypeCoverage.signature_backed c env sig t (List.mem_append_right _ ht)
    let blockC : context := {c with LABELS:=sig.outputs::c.LABELS}
    let loopC : context := {c with LABELS:=sig.inputs::c.LABELS}
    let blockGen := child blockC (env.pushLabel sig.outputs ho) sig.inputs sig.outputs
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c blockC t rfl (hi t ht))
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c blockC t rfl (ho t ht))
    let loopGen := child loopC (env.pushLabel sig.inputs hi) sig.inputs sig.outputs
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c loopC t rfl (hi t ht))
      (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c loopC t rfl (ho t ht))
    [ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,sig.inputs) (.NoEllipses,sig.outputs) hi ho
      (blockGen.map fun code => ⟨.BLOCK sig.raw code.val,fun n => ConstructiveBodyControl.block c stack sig code.val n (code.property n)⟩),
     ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,sig.inputs) (.NoEllipses,sig.outputs) hi ho
      (loopGen.map fun code => ⟨.LOOP sig.raw code.val,fun n => ConstructiveBodyControl.loop c stack sig code.val n (code.property n)⟩),
     ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,sig.inputs++[.NumT .I32T]) (.NoEllipses,sig.outputs)
      (by intro t ht; rcases List.mem_append.mp ht with ht|ht
          · exact hi t ht
          · have he : t=.NumT .I32T := by simpa using ht
            subst t; intro heap hh; cases hh) ho
      (blockGen.bind fun yes => blockGen.map fun no =>
        ⟨.«IF % % ELSE %» sig.raw yes.val no.val,fun n => ConstructiveBodyControl.ifElse c stack sig yes.val no.val n (yes.property n) (no.property n)⟩)]

#print axioms controls
end properties.wasm_module_ok.ConstructiveBodyControlProductions
