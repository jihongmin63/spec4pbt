import properties.wasm_module_ok.ConstructiveBodyControlProductions
import properties.wasm_module_ok.ConstructiveBodyTail
import properties.wasm_module_ok.ConstructiveBodyNumericAtoms
import properties.wasm_module_ok.ConstructiveBodyChoice
import properties.wasm_module_ok.ConstructiveBodyTryTable
import properties.wasm_module_ok.ConstructiveBodyUnaryGeneration
import properties.wasm_module_ok.ConstructiveBodyConversionGeneration
import properties.wasm_module_ok.ConstructiveBodyVectorBinaryGeneration
import properties.wasm_module_ok.ConstructiveBodyVectorLaneGeneration
import properties.wasm_module_ok.ConstructiveBodyBranchTable
import properties.wasm_module_ok.ConstructiveBodyFunctionProductions
import properties.wasm_module_ok.ConstructiveBodyBulkProductions
import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
import properties.wasm_module_ok.ConstructiveBodyCasts
import properties.wasm_module_ok.ConstructiveBodySelectProductions
import properties.wasm_module_ok.ConstructiveBodyReferenceBranches
import properties.wasm_module_ok.ConstructiveBodyMemoryProductions
import properties.wasm_module_ok.ConstructiveBodyAggregateNew
import properties.wasm_module_ok.ConstructiveBodyAggregateCatalog
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyGeneration
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyTail ConstructiveConstTableCore

/-- All instruction families, organized by already established type metadata.
The fixed-array count is a structural plan bound, unbounded in `generate`. -/
def catalog (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (depth : Nat) (child : ConstructiveBodyControlProductions.Builder) : List (Production c stack) :=
  ConstructiveBodySimpleAtoms.plain c stack env hs ++ ConstructiveBodySimpleAtoms.locals c stack env ++
    ConstructiveBodyIndexedProductions.all c stack env ++ ConstructiveBodyBranchTable.productions c stack env hs ++
    ConstructiveBodyFunctionProductions.all c stack env ++ ConstructiveBodyBulkProductions.all c stack env ++
    ConstructiveBodyReferenceProductions.all c stack env hs ++ ConstructiveBodyCasts.all c stack env ++
    ConstructiveBodySelectProductions.all c stack env hs ++ ConstructiveBodyReferenceBranches.all c stack env hs ++ ConstructiveBodyMemoryProductions.all c stack env ++ ConstructiveBodyAggregateNew.all c stack env depth ++ ConstructiveBodyAggregateCatalog.all c stack env ++
    ConstructiveBodyNumericAtoms.literals c stack env ++ ConstructiveBodyOperatorProductions.all c stack env ++
    ConstructiveBodyUnaryGeneration.all c stack env ++ ConstructiveBodyConversionGeneration.all c stack env ++
    [ConstructiveBodyVectorBinaryGeneration.production c stack env] ++ ConstructiveBodyVectorLaneGeneration.all c stack env ++
    ConstructiveBodyControlProductions.controls c stack env child ++ ConstructiveBodyTryTable.controls c stack env child

/-- Sound grammar containing every raw opcode family. Full mutual original
body completeness is established separately before Contract integration. -/
def sized : (depth : Nat) → (root c : context) → (stack : inferresulttype) → (outputs : List valtype) →
    Env root → Env c → StackBacked c stack →
    (∀t∈outputs,CandidateValMatch.InTableVal root t) → c.TYPES=root.TYPES →
    Audited (Tail root c stack outputs)
  | 0,root,c,stack,outputs,er,ec,hs,ho,he =>
      endings root c stack outputs er
        (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c root t he.symm (hs t ht)) ho
  | depth+1,root,c,stack,outputs,er,ec,hs,ho,he =>
      let child : ConstructiveBodyControlProductions.Builder := fun d ed ins outs hi ho =>
        -- Defer structural sub-generation until its production is selected.
        (Audited.pure ()).bind fun _ =>
          (sized depth d d (.NoEllipses,ins) outs ed ed hi ho rfl).map asBlock
      let productions := catalog c stack ec hs depth child
      let choices := productions.flatMap fun p =>
        match prepare c stack ec hs p with
        | none => []
        | some g => [g.bind fun step =>
          (sized depth root step.nextContext step.nextStack outputs er step.nextEnv step.nextBacked ho
            (step.typesEq.trans he)).map (prepend step)]
      ConstructiveBodyChoice.branches (sized depth root c stack outputs er ec hs ho he) choices

theorem sized_succ (depth : Nat) (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (er : Env root) (ec : Env c) (hs : StackBacked c stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
    (tail : Tail root c stack outputs)
    (h : Gen.support (sized depth root c stack outputs er ec hs ho he).generator tail) :
    Gen.support (sized (depth+1) root c stack outputs er ec hs ho he).generator tail := by
  change Gen.support (ConstructiveBodyChoice.branches (sized depth root c stack outputs er ec hs ho he) _).generator tail
  apply (ConstructiveBodyChoice.branches_support _ _ _).mpr
  exact ⟨_,List.mem_cons_self,h⟩

theorem sized_monotone (depth extra : Nat) (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (er : Env root) (ec : Env c) (hs : StackBacked c stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
    (tail : Tail root c stack outputs)
    (h : Gen.support (sized depth root c stack outputs er ec hs ho he).generator tail) :
    Gen.support (sized (depth+extra) root c stack outputs er ec hs ho he).generator tail := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact sized_succ (depth+extra) root c stack outputs er ec hs ho he tail ih

def generate (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t)
    (ho : ∀t∈outs,CandidateValMatch.InTableVal c t) : Gen (ConstructiveBodyControlProductions.Body c ins outs) := do
  let depth ← Gen.arbNat
  ((sized depth c c (.NoEllipses,ins) outs env env hi ho rfl).map asBlock).generator

def bodies (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t)
    (ho : ∀t∈outs,CandidateValMatch.InTableVal c t) : Gen (List instr) :=
  Subtype.val <$> generate c env ins outs hi ho

theorem generate_audit (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t)
    (ho : ∀t∈outs,CandidateValMatch.InTableVal c t) :
    ConstructiveGenAudit.Structural (generate c env ins outs hi ho) := by
  exact ⟨by simp,fun depth => ((sized depth c c (.NoEllipses,ins) outs env env hi ho rfl).map asBlock).audit⟩

theorem bodies_sound (c : context) (env : Env c) (ins outs : List valtype)
    (hi : ∀t∈ins,CandidateValMatch.InTableVal c t)
    (ho : ∀t∈outs,CandidateValMatch.InTableVal c t) (code : List instr)
    (h : Gen.support (bodies c env ins outs hi ho) code) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Block_ok c (.InstrT ins outs []) code⟩)
      n (.success (.of ())) n := by
  simp only [bodies,Gen.Support.support_map] at h
  obtain ⟨b,_,rfl⟩ := h
  exact b.property n

#print axioms bodies_sound
#print axioms sized_monotone
#print axioms generate_audit
end properties.wasm_module_ok.ConstructiveBodyGeneration
