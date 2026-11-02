import properties.wasm_module_ok.ConstructiveBodyProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySimpleAtoms
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveConstTableCore

def unchanged (c : context) (stack : inferresulttype) (env : Env c)
    (ins outs : inferresulttype) (hi : StackBacked c ins) (ho : StackBacked c outs)
    (g : Audited {i : instr // ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of ((⟨ins,outs⟩,[]) : inferinstrtype))) n}) : Production c stack :=
  ⟨(⟨ins,outs⟩,[]),c,env,rfl,hi,ho,LocalInitValidation.init_locals_nil_total c,g⟩

theorem nop_call (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .NOP⟩)
      n (.success (.of ((⟨(.NoEllipses,[]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack .NOP 1 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:1» c stack .NOP) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem drop_call (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .DROP⟩)
      n (.success (.of ((⟨(.NoEllipses,[PeekDecision.peekResult 0 stack]),(.NoEllipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack .DROP 2 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:2» c stack .DROP) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:2»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekDecision.peek_total 0 stack n)
  exact SpecTecExecution.Eval.pure _

theorem return_call (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .RETURN⟩)
      n (.success (.of ((⟨(.Ellipses,c.RESULTS),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack .RETURN 18 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:18» c stack .RETURN) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:18»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem throwRef_call (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .THROW_REF⟩)
      n (.success (.of ((⟨(.Ellipses,[.RefT (.«% %» .Null .ExnHT)]),(.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack .THROW_REF 23 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:23» c stack .THROW_REF) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:23»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem localGet_call (c : context) (stack : inferresulttype) (x : Nat) (t : valtype) (n : Nat)
    (hx : c.LOCALS[x]?=some (.LocalT .Set t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«LOCAL.GET» x)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [] [t] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.GET» x) 25 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:25» c stack (.«LOCAL.GET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:25»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem localSet_call (c : context) (stack : inferresulttype) (x : Nat) (ini : init) (t : valtype) (n : Nat)
    (hx : c.LOCALS[x]?=some (.LocalT ini t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«LOCAL.SET» x)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [t] [] [x]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.SET» x) 26 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:26» c stack (.«LOCAL.SET» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:26»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  exact SpecTecExecution.Eval.pure _

theorem localTee_call (c : context) (stack : inferresulttype) (x : Nat) (ini : init) (t : valtype) (n : Nat)
    (hx : c.LOCALS[x]?=some (.LocalT ini t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«LOCAL.TEE» x)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [t] [t] [x]))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«LOCAL.TEE» x) 27 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:27» c stack (.«LOCAL.TEE» x)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:27»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  exact SpecTecExecution.Eval.pure _

theorem peek_backed (c : context) (stack : inferresulttype) (hs : StackBacked c stack) (j : Nat) :
    CandidateValMatch.InTableVal c (PeekDecision.peekResult j stack) := by
  unfold PeekDecision.peekResult
  cases he : stack.2.reverse[j]? with
  | none => intro ht hm; cases hm
  | some t =>
    exact hs t (List.mem_reverse.mp (List.mem_iff_getElem?.mpr ⟨j,he⟩))

def plain (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    List (Production c stack) :=
  [unchanged c stack env (.Ellipses,[]) (.Ellipses,[]) (by simp [StackBacked]) (by simp [StackBacked])
    (Audited.pure ⟨.UNREACHABLE,UnreachableValidation.unreachable_instr_total c stack⟩),
   unchanged c stack env (.NoEllipses,[]) (.NoEllipses,[]) (by simp [StackBacked]) (by simp [StackBacked])
    (Audited.pure ⟨.NOP,nop_call c stack⟩),
   unchanged c stack env (.NoEllipses,[PeekDecision.peekResult 0 stack]) (.NoEllipses,[])
    (by intro t ht; have he : t=PeekDecision.peekResult 0 stack := by simpa using ht
        subst t; exact peek_backed c stack hs 0) (by simp [StackBacked])
    (Audited.pure ⟨.DROP,drop_call c stack⟩),
   unchanged c stack env (.Ellipses,c.RESULTS) (.Ellipses,[]) env.results (by simp [StackBacked])
    (Audited.pure ⟨.RETURN,return_call c stack⟩),
   unchanged c stack env (.Ellipses,[.RefT (.«% %» .Null .ExnHT)]) (.Ellipses,[])
    (by intro t ht; have he : t=.RefT (.«% %» .Null .ExnHT) := by simpa using ht
        subst t; exact CandidateValMembership.valid_candidate_in_table c _ (by simp [FiniteValidTypes.validCandidates,FiniteValidTypes.refCandidates,FiniteValidTypes.heapCandidates,HeaptypeValidation.baseHeaptypes]))
    (by simp [StackBacked]) (Audited.pure ⟨.THROW_REF,throwRef_call c stack⟩)]

def localGet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (t : valtype)
    (hx : c.LOCALS[x]?=some (.LocalT .Set t)) : Production c stack :=
  unchanged c stack env (.NoEllipses,[]) (.NoEllipses,[t]) (by simp [StackBacked])
    (by intro u hu; have he : u=t := by simpa using hu
        subst u; exact env.locals .Set t (List.mem_iff_getElem?.mpr ⟨x,hx⟩))
    (Audited.pure ⟨.«LOCAL.GET» x,fun n => localGet_call c stack x t n hx⟩)

def localWrite (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (ini : init) (t : valtype)
    (hx : c.LOCALS[x]?=some (.LocalT ini t)) (tee : Bool) : Production c stack := by
  have ht : CandidateValMatch.InTableVal c t := env.locals ini t (List.mem_iff_getElem?.mpr ⟨x,hx⟩)
  let next : context := {c with LOCALS:=c.LOCALS.set x (.LocalT .Set t)}
  have hi : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTecCall.«$init_locals» c [x]⟩) n (.success (.of next)) n := by
    intro n
    apply (LocalInitValidation.init_locals_success_iff_result c [x] next n n).2
    exact ⟨by simp [LocalInitValidation.initLocalsResult,LocalInitValidation.initLocalResult,hx,next],rfl⟩
  cases tee with
  | false =>
    exact ⟨ConstructiveBodyControl.effect [t] [] [x],next,env.setLocal x t ht,rfl,
      by intro u hu; have he : u=t := by simpa [ConstructiveBodyControl.effect] using hu
         subst u; exact ht,
      by simp [StackBacked,ConstructiveBodyControl.effect],hi,
      Audited.pure ⟨.«LOCAL.SET» x,fun n => localSet_call c stack x ini t n hx⟩⟩
  | true =>
    exact ⟨ConstructiveBodyControl.effect [t] [t] [x],next,env.setLocal x t ht,rfl,
      by intro u hu; have he : u=t := by simpa [ConstructiveBodyControl.effect] using hu
         subst u; exact ht,
      by intro u hu; have he : u=t := by simpa [ConstructiveBodyControl.effect] using hu
         subst u; exact ht,hi,
      Audited.pure ⟨.«LOCAL.TEE» x,fun n => localTee_call c stack x ini t n hx⟩⟩

def locals (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (List.finRange c.LOCALS.length).flatMap fun x =>
    match hx : c.LOCALS[x.val] with
    | .LocalT ini t =>
      let hget : c.LOCALS[x.val]?=some (.LocalT ini t) := by simp [hx]
      [localWrite c stack env x.val ini t hget false,localWrite c stack env x.val ini t hget true] ++
      match hi : ini with
      | .Set => [localGet c stack env x.val t (by simpa [hi] using hget)]
      | .Unset => []

#print axioms localWrite
#print axioms plain
end properties.wasm_module_ok.ConstructiveBodySimpleAtoms
