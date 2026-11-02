import properties.wasm_module_ok.ConstructiveBodyTagMetadata
import properties.wasm_module_ok.ConstructiveLists
import properties.wasm_module_ok.ConstructiveBodyChoice
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCatches
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyTagMetadata ConstructiveConstTableCore

theorem call_Catch (c : context) (tag : Tag c) (outputs : List valtype)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES tag.inputs target⟩)
      n (.success (.of true)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Catch_ok c outputs (.Catch tag.index y)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Catch_ok_clauses c outputs (.Catch tag.index y)) ()) n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:0» c outputs (.Catch tag.index y)) n (.success (.of ())) n
  unfold SpecTec.«Catch_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp tag.lookup).1)
  rw [tag.lookup]
  apply SpecTecExecution.Eval.bind_success
    ((UnrollInterface.expanddt_success_iff_result tag.definition (.DefFuncT (.FuncT tag.inputs tag.outputs)) n n).2 ⟨tag.expanded,rfl⟩)
  apply SpecTecExecution.Eval.bind_success
    ((StartValidation.functype_of_strtype_success_iff (.DefFuncT (.FuncT tag.inputs tag.outputs)) (.FuncT tag.inputs tag.outputs) n n).2 ⟨rfl,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success hm
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure ()

theorem call_CatchRef (c : context) (tag : Tag c) (outputs : List valtype)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES (tag.inputs++[exn]) target⟩)
      n (.success (.of true)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Catch_ok c outputs (.CatchRef tag.index y)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Catch_ok_clauses c outputs (.CatchRef tag.index y)) ()) n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:0» c outputs (.CatchRef tag.index y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:Catch»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:1» c outputs (.CatchRef tag.index y)) n (.success (.of ())) n
  unfold SpecTec.«Catch_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp tag.lookup).1)
  rw [tag.lookup]
  apply SpecTecExecution.Eval.bind_success
    ((UnrollInterface.expanddt_success_iff_result tag.definition (.DefFuncT (.FuncT tag.inputs tag.outputs)) n n).2 ⟨tag.expanded,rfl⟩)
  apply SpecTecExecution.Eval.bind_success
    ((StartValidation.functype_of_strtype_success_iff (.DefFuncT (.FuncT tag.inputs tag.outputs)) (.FuncT tag.inputs tag.outputs) n n).2 ⟨rfl,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success hm
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure ()

theorem call_CatchAll (c : context) (outputs : List valtype)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES [] target⟩)
      n (.success (.of true)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Catch_ok c outputs (.CatchAll y)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Catch_ok_clauses c outputs (.CatchAll y)) ()) n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:0» c outputs (.CatchAll y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:Catch»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:1» c outputs (.CatchAll y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:CatchRef»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:2» c outputs (.CatchAll y)) n (.success (.of ())) n
  unfold SpecTec.«Catch_ok:clause:2»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success hm
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure ()

theorem call_CatchAllRef (c : context) (outputs : List valtype)
    (y : Nat) (target : List valtype) (hy : c.LABELS[y]?=some target) (n : Nat)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES [exn] target⟩)
      n (.success (.of true)) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Catch_ok c outputs (.CatchAllRef y)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Catch_ok_clauses c outputs (.CatchAllRef y)) ()) n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:0» c outputs (.CatchAllRef y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:Catch»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:1» c outputs (.CatchAllRef y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:CatchRef»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:2» c outputs (.CatchAllRef y)) n .unmatch n
    unfold SpecTec.«Catch_ok:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:catch:CatchAll»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Catch_ok:clause:3» c outputs (.CatchAllRef y)) n (.success (.of ())) n
  unfold SpecTec.«Catch_ok:clause:3»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hy).1)
  rw [hy]
  apply SpecTecExecution.Eval.bind_success hm
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure ()

abbrev Handler (c : context) := {x : SpecTec.«catch» // ∀outputs n,
  SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨Unit,SpecTecCall.Catch_ok c outputs x⟩) n (.success (.of ())) n}

def specific (c : context) (env : Env c) (tag : Tag c) (withRef : Bool)
    (y : Fin c.LABELS.length)
    (hm : MatchResulttypeDecision.matchPairs c (arguments tag withRef) c.LABELS[y.val]=true) : Handler c := by
  have hmatch (n : Nat) : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES (arguments tag withRef) c.LABELS[y.val]⟩)
      n (.success (.of true)) n := by
    simpa only [hm] using ConstructiveBodyMatchers.result_total c (arguments tag withRef) c.LABELS[y.val] n
      env.ready (arguments_backed tag env withRef) (env.labels _ (List.getElem_mem _))
  cases withRef with
  | false => exact ⟨.Catch tag.index y.val,fun outputs n => call_Catch c tag outputs y.val c.LABELS[y.val] (by simp) n
      (by simpa [arguments] using hmatch n)⟩
  | true => exact ⟨.CatchRef tag.index y.val,fun outputs n => call_CatchRef c tag outputs y.val c.LABELS[y.val] (by simp) n
      (by simpa [arguments] using hmatch n)⟩

def all (c : context) (env : Env c) (withRef : Bool) (y : Fin c.LABELS.length)
    (hm : MatchResulttypeDecision.matchPairs c (if withRef then [exn] else []) c.LABELS[y.val]=true) : Handler c := by
  have hbacked : ∀t∈(if withRef then [exn] else []),CandidateValMatch.InTableVal c t := by
    cases withRef with
    | false => simp
    | true => intro t ht; have he : t=exn := by simpa using ht
              subst t; exact exn_backed c
  have hmatch (n : Nat) : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_resulttype» c.TYPES (if withRef then [exn] else []) c.LABELS[y.val]⟩)
      n (.success (.of true)) n := by
    simpa only [hm] using ConstructiveBodyMatchers.result_total c _ c.LABELS[y.val] n
      env.ready hbacked (env.labels _ (List.getElem_mem _))
  cases withRef with
  | false => exact ⟨.CatchAll y.val,fun outputs n => call_CatchAll c outputs y.val c.LABELS[y.val] (by simp) n (hmatch n)⟩
  | true => exact ⟨.CatchAllRef y.val,fun outputs n => call_CatchAllRef c outputs y.val c.LABELS[y.val] (by simp) n (hmatch n)⟩

/-- Legal tag/label combinations are chosen by their type metadata before a
catch constructor is emitted. Original rule order is proved above. -/
def handlers (c : context) (env : Env c) : List (Handler c) :=
  (List.finRange c.LABELS.length).flatMap fun y =>
    ([false,true].flatMap fun withRef =>
      if hm : MatchResulttypeDecision.matchPairs c (if withRef then [exn] else []) c.LABELS[y.val]=true
      then [all c env withRef y hm] else []) ++
    (tags c).flatMap fun tag =>
      [false,true].flatMap fun withRef =>
        if hm : MatchResulttypeDecision.matchPairs c (arguments tag withRef) c.LABELS[y.val]=true
        then [specific c env tag withRef y hm] else []

def lists (c : context) (env : Env c) : Audited (List (Handler c)) :=
  match handlers c env with
  | [] => Audited.pure []
  | h::t =>
    let g := ConstructiveBodyChoice.branches (Audited.pure h) (t.map Audited.pure)
    ⟨ConstructiveLists.all g.generator,ConstructiveLists.all_audit g.generator g.audit⟩

#print axioms handlers
#print axioms lists
end properties.wasm_module_ok.ConstructiveBodyCatches
