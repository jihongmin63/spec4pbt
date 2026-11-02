import properties.wasm_module_ok.ConstructiveBodyInitTypes
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
import properties.wasm_module_ok.ConstructiveBodyChoice
import properties.wasm_module_ok.ConstructiveBodyMatchers
import properties.wasm_module_ok.ConstructiveLists
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBranchTable
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyLookup

/-- A bounded label index paired with its already compatible type metadata. -/
structure Target (c : context) (actual : List valtype) where
  entry : Entry c.LABELS
  matched : MatchResulttypeDecision.matchPairs c actual entry.value=true

/-- Select compatible label signatures before sampling any branch instruction. -/
def targets (c : context) (actual : List valtype) : List (Target c actual) :=
  (entries c.LABELS).flatMap fun e =>
    if hm : MatchResulttypeDecision.matchPairs c actual e.value=true then [⟨e,hm⟩] else []

theorem targets_complete (c : context) (actual : List valtype) (t : Target c actual) : t∈targets c actual := by
  apply List.mem_flatMap.mpr
  refine ⟨t.entry,ConstructiveBodyLookup.complete _ t.entry,?_⟩
  simp only [t.matched,dif_pos]
  exact List.mem_singleton_self _

def choices (c : context) (actual : List valtype) (base : Target c actual) : Audited (Target c actual) :=
  ConstructiveBodyChoice.branches (Audited.pure base) ((targets c actual).map Audited.pure)

theorem choices_complete (c : context) (actual : List valtype) (base target : Target c actual) :
    Gen.support (choices c actual base).generator target := by
  apply (ConstructiveBodyChoice.branches_support _ _ _).2
  exact ⟨Audited.pure target,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨target,targets_complete c actual target,rfl⟩),rfl⟩

def lists (c : context) (actual : List valtype) (base : Target c actual) : Audited (List (Target c actual)) :=
  ⟨ConstructiveLists.all (choices c actual base).generator,
    ConstructiveLists.all_audit _ (choices c actual base).audit⟩

theorem lists_complete (c : context) (actual : List valtype) (base : Target c actual) (xs : List (Target c actual)) :
    Gen.support (lists c actual base).generator xs :=
  (ConstructiveLists.all_support _ _).2 (fun x _ => choices_complete c actual base x)

def indices {c : context} {actual : List valtype} (xs : List (Target c actual)) : List Nat := xs.map (fun t => t.entry.index)

theorem bounds (c : context) (actual : List valtype) (xs : List (Target c actual)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.«Instr_ok:br_table:iter:3» c (indices xs)⟩) n (.success (.of ())) n := by
  induction xs with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:3_clauses» c []) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure _
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:3_clauses» c (x.entry.index::indices xs)) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact SpecTecExecution.Eval.unmatch
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«Instr_ok:br_table:iter:3:clause:1»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp x.entry.lookup).1)
    exact SpecTecExecution.Eval.bind_success ih (SpecTecExecution.Eval.pure _)

theorem targets_call (c : context) (actual : List valtype) (xs : List (Target c actual))
    (env : Env c) (ha : ∀t∈actual,CandidateValMatch.InTableVal c t) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.«Instr_ok:br_table:iter:4» c actual (indices xs)⟩) n (.success (.of ())) n := by
  induction xs with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:4_clauses» c actual []) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure _
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«Instr_ok:br_table:iter:4_clauses» c actual (x.entry.index::indices xs)) ()) n (.success (.of ())) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact SpecTecExecution.Eval.unmatch
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«Instr_ok:br_table:iter:4:clause:1»
    simp only [x.entry.lookup]
    apply SpecTecExecution.Eval.bind_success
      ((MatchResulttypeDecision.match_pairs_iff_resulttype c actual x.entry.value n env.ready ha
        (env.labels x.entry.value x.entry.mem)).1 x.matched)
    exact SpecTecExecution.Eval.bind_success ih (SpecTecExecution.Eval.pure _)

theorem branchTable (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (base : Entry c.LABELS)
    (hm : MatchResulttypeDecision.matchPairs c (ConstructiveBodyInitTypes.operandTypes stack base.value.length) base.value=true)
    (xs : List (Target c (ConstructiveBodyInitTypes.operandTypes stack base.value.length))) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_TABLE (indices xs) base.index)⟩)
      n (.success (.of ((⟨(.Ellipses,ConstructiveBodyInitTypes.operandTypes stack base.value.length++[.NumT .I32T]),
        (.Ellipses,[])⟩,[]) : inferinstrtype))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_TABLE (indices xs) base.index) 10 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instr_ok:clause:10» c stack (.BR_TABLE (indices xs) base.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:10»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp base.lookup).1)
  rw [base.lookup]
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyInitTypes.zero_call stack base.value.length n)
  simp only [base.lookup]
  apply SpecTecExecution.Eval.bind_success
    ((MatchResulttypeDecision.match_pairs_iff_resulttype c _ base.value n env.ready
      (ConstructiveBodyInitTypes.prefix_backed c stack hs _) (env.labels base.value base.mem)).1 hm)
  apply SpecTecExecution.Eval.bind_success (bounds c _ xs n)
  exact SpecTecExecution.Eval.bind_success (targets_call c _ xs env (ConstructiveBodyInitTypes.prefix_backed c stack hs _) n) (SpecTecExecution.Eval.pure _)

def production (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (base : Entry c.LABELS)
    (hm : MatchResulttypeDecision.matchPairs c (ConstructiveBodyInitTypes.operandTypes stack base.value.length) base.value=true) : Production c stack :=
  let actual := ConstructiveBodyInitTypes.operandTypes stack base.value.length
  ConstructiveBodySimpleAtoms.unchanged c stack env (.Ellipses,actual++[.NumT .I32T]) (.Ellipses,[])
    (ConstructiveBodyIndexedProductions.append_backed .Ellipses (ConstructiveBodyInitTypes.prefix_backed c stack hs _)
      (ConstructiveBodyIndexedProductions.cons_backed .NoEllipses (ConstructiveBodyIndexedProductions.num_backed c _) (ConstructiveBodyIndexedProductions.nil_backed c .NoEllipses)))
    (ConstructiveBodyIndexedProductions.nil_backed c .Ellipses)
    ((lists c actual ⟨base,hm⟩).map fun xs => ⟨.BR_TABLE (indices xs) base.index,fun n => branchTable c stack env hs base hm xs n⟩)

def productions (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) : List (Production c stack) :=
  (entries c.LABELS).flatMap fun base =>
    if hm : MatchResulttypeDecision.matchPairs c (ConstructiveBodyInitTypes.operandTypes stack base.value.length) base.value=true then
      [production c stack env hs base hm]
    else []

#print axioms branchTable
#print axioms lists_complete
end properties.wasm_module_ok.ConstructiveBodyBranchTable
