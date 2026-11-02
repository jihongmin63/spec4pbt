import properties.wasm_module_ok.ConstructiveBodyGeneration
import properties.wasm_module_ok.ConstructiveBodyEndingCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySizedSupport
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyTail ConstructiveBodyGeneration ConstructiveConstTableCore

/-- The recursive builder is exactly the delayed child used by `sized`. -/
def child (depth : Nat) : ConstructiveBodyControlProductions.Builder := fun c env ins outs hi ho =>
  (Audited.pure ()).bind fun _ =>
    (sized depth c c (.NoEllipses,ins) outs env env hi ho rfl).map asBlock

theorem monotone (low high : Nat) (hle : low≤high) (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (er : Env root) (ec : Env c) (hs : StackBacked c stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
    (tail : Tail root c stack outputs)
    (h : Gen.support (sized low root c stack outputs er ec hs ho he).generator tail) :
    Gen.support (sized high root c stack outputs er ec hs ho he).generator tail := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le hle
  exact sized_monotone low extra root c stack outputs er ec hs ho he tail h

theorem ending (depth : Nat) (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (er : Env root) (ec : Env c) (hs : StackBacked c stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
    (ell : ellipses) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferresulttype,Call.«$pop» root (.NoEllipses,outputs) stack⟩)
      n (.success (.of ((ell,[]) : inferresulttype))) finish) :
    (∃tail,Gen.support (sized depth root c stack outputs er ec hs ho he).generator tail ∧ tail.val=[]) ∧ finish=n := by
  obtain ⟨⟨tail,ht,hval⟩,hn⟩ := ConstructiveBodyEndingCoverage.original root c stack outputs er
    (fun t ht => CandidateProvenanceSteps.in_table_val_of_types_eq c root t he.symm (hs t ht)) ho ell n finish h
  exact ⟨⟨tail,monotone 0 depth (Nat.zero_le _) root c stack outputs er ec hs ho he tail ht,hval⟩,hn⟩

theorem cons (depth : Nat) (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (er : Env root) (ec : Env c) (hs : StackBacked c stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (he : c.TYPES=root.TYPES)
    (p : Production c stack) (hp : p∈catalog c stack ec hs depth (child depth))
    (g : Audited (Step c stack)) (hg : prepare c stack ec hs p=some g)
    (step : Step c stack) (hstep : Gen.support g.generator step)
    (tail : Tail root step.nextContext step.nextStack outputs)
    (htail : Gen.support (sized depth root step.nextContext step.nextStack outputs er step.nextEnv step.nextBacked ho
      (step.typesEq.trans he)).generator tail) :
    Gen.support (sized (depth+1) root c stack outputs er ec hs ho he).generator (prepend step tail) := by
  change Gen.support (ConstructiveBodyChoice.branches (sized depth root c stack outputs er ec hs ho he) _).generator _
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  let chosen := g.bind fun step =>
    (sized depth root step.nextContext step.nextStack outputs er step.nextEnv step.nextBacked ho
      (step.typesEq.trans he)).map (prepend step)
  refine ⟨chosen,?mem,?support⟩
  case mem =>
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨p,hp,?_⟩
    simp only [hg]
    exact List.mem_singleton_self _
  case support => exact ⟨step,hstep,tail,htail,rfl⟩

#print axioms cons
#print axioms ending
end properties.wasm_module_ok.ConstructiveBodySizedSupport
