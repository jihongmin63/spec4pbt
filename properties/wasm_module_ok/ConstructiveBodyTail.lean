import properties.wasm_module_ok.ConstructiveBodyProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTail
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveConstTableCore

/-- A completed continuation, with the caller's final-pop context retained
separately from the context whose locals change during the instruction trace. -/
abbrev Tail (root c : context) (stack : inferresulttype) (outputs : List valtype) :=
  {code : List instr // ∀n,∃finalContext finalStack ell,
    ConstConstructiveTrace.Trace c stack code finalContext finalStack n n ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferresulttype,SpecTecCall.«$pop» root (.NoEllipses,outputs) finalStack⟩)
      n (.success (.of ((ell,[]) : inferresulttype))) n}

def unreachable (root c : context) (stack : inferresulttype) (outputs : List valtype) :
    Tail root c stack outputs :=
  ⟨[.UNREACHABLE],by
    intro n
    refine ⟨c,(.Ellipses,[]),.Ellipses,?_,UnreachableValidation.pop_ellipsis_empty_total root outputs n⟩
    apply ConstConstructiveTrace.Trace.cons
      (UnreachableValidation.unreachable_instr_total c stack n)
      (LocalInitValidation.init_locals_nil_total c n)
      (ConstructiveBodyCompletion.pop_unreachable_total c stack n)
    · simpa only [PushValidation.pushOutcome,PushValidation.pushResult] using
        PushValidation.push_total c (.Ellipses,[]) (stack.1,[]) n
    · exact ConstConstructiveTrace.Trace.nil c (.Ellipses,[]) n⟩

def stop (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (env : Env root) (hs : StackBacked root stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (ell : ellipses)
    (hp : ConstructiveBodyPopPlans.popPlan root (.NoEllipses,outputs) stack=some (ell,[])) :
    Tail root c stack outputs :=
  ⟨[],fun n => ⟨c,stack,ell,ConstConstructiveTrace.Trace.nil c stack n,
    ConstructiveBodyPopPlans.pop_plan_sound root (.NoEllipses,outputs) stack (ell,[]) n env.ready ho hs hp⟩⟩

/-- A normal ending is offered exactly when its stack type closes. The other
branch constructs an explicit UNREACHABLE instruction and never repairs code. -/
def endings (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (env : Env root) (hs : StackBacked root stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) : Audited (Tail root c stack outputs) :=
  match hp : ConstructiveBodyPopPlans.popPlan root (.NoEllipses,outputs) stack with
  | some (ell,[]) => (Audited.pure (stop root c stack outputs env hs ho ell hp)).pick
      (Audited.pure (unreachable root c stack outputs))
  | _ => Audited.pure (unreachable root c stack outputs)

def prepend {root c : context} {stack : inferresulttype} {outputs : List valtype}
    (step : Step c stack) (tail : Tail root step.nextContext step.nextStack outputs) :
    Tail root c stack outputs :=
  ⟨step.instruction::tail.val,by
    intro n
    obtain ⟨finalContext,finalStack,ell,htrace,hpop⟩ := tail.property n
    exact ⟨finalContext,finalStack,ell,
      ConstConstructiveTrace.trace_append (step.trace n) htrace,hpop⟩⟩

def asBlock {c : context} {inputs outputs : List valtype}
    (tail : Tail c c (.NoEllipses,inputs) outputs) :
    {code : List instr // ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Block_ok c (.InstrT inputs outputs []) code⟩)
      n (.success (.of ())) n} :=
  ⟨tail.val,by
    intro n
    obtain ⟨_,finalStack,ell,htrace,hpop⟩ := tail.property n
    exact (BlockTrace.block_success_iff c inputs outputs [] tail.val n n).2
      ⟨finalStack,[],ell,n,ConstConstructiveTrace.trace_to_instrs htrace,hpop⟩⟩

#print axioms asBlock
#print axioms prepend
end properties.wasm_module_ok.ConstructiveBodyTail
