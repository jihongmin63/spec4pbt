import properties.wasm_module_ok.ConstructiveBodyEnvironment
import properties.wasm_module_ok.ConstructiveBodyCompletion
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstTableCore

/-- A production is an instruction family with fixed type metadata. Its
instruction generator is sampled only after stack-compatible selection. -/
structure Production (c : context) (stack : inferresulttype) where
  effect : inferinstrtype
  nextContext : context
  nextEnv : Env nextContext
  typesEq : nextContext.TYPES=c.TYPES
  inputsBacked : StackBacked c effect.1.INS
  outputsBacked : StackBacked c effect.1.OUTS
  initialized : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨context,SpecTecCall.«$init_locals» c effect.2⟩)
    n (.success (.of nextContext)) n
  instructions : Audited {i : instr // ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
    n (.success (.of effect)) n}

structure Step (c : context) (stack : inferresulttype) where
  instruction : instr
  nextContext : context
  nextStack : inferresulttype
  nextEnv : Env nextContext
  typesEq : nextContext.TYPES=c.TYPES
  nextBacked : StackBacked nextContext nextStack
  trace : ∀n,ConstConstructiveTrace.Trace c stack [instruction] nextContext nextStack n n

theorem remaining_backed (c : context) (need stack : inferresulttype)
    (hs : StackBacked c stack) : StackBacked c (ConstructiveBodyPopPlans.remaining need stack) := by
  intro t ht
  unfold ConstructiveBodyPopPlans.remaining at ht
  cases he : need.1 with
  | Ellipses => simp [he] at ht
  | NoEllipses => simp only [he] at ht; exact hs t (List.mem_of_mem_take ht)

theorem pushed_backed (c : context) (outs remaining next : inferresulttype)
    (ho : StackBacked c outs) (hr : StackBacked c remaining)
    (h : PushValidation.pushResult outs remaining=some next) : StackBacked c next := by
  rcases outs with ⟨oe,os⟩
  rcases remaining with ⟨re,rs⟩
  cases oe with
  | NoEllipses =>
    cases re <;> simp only [PushValidation.pushResult] at h <;> cases h
    all_goals
      intro t ht
      rcases List.mem_append.mp ht with hm|hm
      · exact hr t hm
      · exact ho t hm
  | Ellipses =>
    cases rs with
    | nil => cases re <;> simp only [PushValidation.pushResult] at h <;> cases h <;> exact ho
    | cons r rs => cases re <;> simp [PushValidation.pushResult] at h

def step (c : context) (stack : inferresulttype) (env : Env c)
    (hs : StackBacked c stack) (p : Production c stack)
    (popped next : inferresulttype)
    (hp : ConstructiveBodyPopPlans.popPlan c p.effect.1.INS stack=some popped)
    (hq : PushValidation.pushResult p.effect.1.OUTS popped=some next)
    (i : {i : instr // ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of p.effect)) n}) : Step c stack :=
  ⟨i.val,p.nextContext,next,p.nextEnv,p.typesEq,by
    have hr : popped=ConstructiveBodyPopPlans.remaining p.effect.1.INS stack := by
      unfold ConstructiveBodyPopPlans.popPlan at hp
      split at hp
      · exact Option.some.inj hp |>.symm
      · cases hp
    subst popped
    intro t ht
    exact CandidateProvenanceSteps.in_table_val_of_types_eq c p.nextContext t p.typesEq
      (pushed_backed c _ _ next p.outputsBacked (remaining_backed c _ stack hs) hq t ht),by
    intro n
    apply ConstConstructiveTrace.Trace.cons (i.property n) (p.initialized n)
      (ConstructiveBodyPopPlans.pop_plan_sound c _ stack popped n env.ready p.inputsBacked hs hp)
      ((PushValidation.push_success_iff_result c p.effect.1.OUTS popped next n n).2 ⟨hq,rfl⟩)
    exact ConstConstructiveTrace.Trace.nil p.nextContext next n⟩

/-- Selection compares already proven type metadata. No instruction result is
validated, discarded, or replaced on a failing metadata alternative. -/
def prepare (c : context) (stack : inferresulttype) (env : Env c)
    (hs : StackBacked c stack) (p : Production c stack) : Option (Audited (Step c stack)) :=
  match hp : ConstructiveBodyPopPlans.popPlan c p.effect.1.INS stack with
  | none => none
  | some popped =>
    match hq : PushValidation.pushResult p.effect.1.OUTS popped with
    | none => none
    | some next => some (p.instructions.map (step c stack env hs p popped next hp hq))

#print axioms step
end properties.wasm_module_ok.ConstructiveBodyProductions
