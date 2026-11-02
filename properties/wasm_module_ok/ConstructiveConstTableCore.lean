import properties.wasm_module_ok.ConstructiveConstAggregateBuilders
import properties.wasm_module_ok.ConstructiveConstLiteralGen
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTableCore
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders

structure Audited (α : Type) where
  generator : Gen α
  audit : Structural generator

def Audited.pure {α : Type} (a : α) : Audited α := ⟨.ret a,trivial⟩
def Audited.map {α β : Type} (f : α → β) (a : Audited α) : Audited β :=
  ⟨f <$> a.generator,(map_audit f a.generator).2 a.audit⟩
def Audited.bind {α β : Type} (a : Audited α) (f : α → Audited β) : Audited β :=
  ⟨a.generator >>= fun x => (f x).generator,⟨a.audit,fun x => (f x).audit⟩⟩
def Audited.pick {α : Type} (a b : Audited α) : Audited α :=
  ⟨Gen.pick a.generator b.generator,⟨a.audit,b.audit⟩⟩
def Audited.merge {α : Type} (head : Audited α) : List (Audited α) → Audited α
  | [] => head
  | x::xs => head.pick (Audited.merge x xs)

theorem merge_support {α : Type} (head : Audited α) (tail : List (Audited α)) (a : α) :
    Gen.support (Audited.merge head tail).generator a ↔
    ∃ g∈head::tail,Gen.support g.generator a := by
  induction tail generalizing head with
  | nil => simp [Audited.merge]
  | cons x xs ih => simp [Audited.merge,Audited.pick,ih]

/-- The runtime table stores types and generators, never arbitrary ASTs to check.
The table-readiness field and recursive structural audit are erased proofs. -/
structure Entry (c : context) where
  type : valtype
  values : Audited (Typed c type)
  inTable : CandidateValMatch.InTableVal c type

def entry (c : context) (hp : CandidateUniverseReady.Provenance c)
    (u : valtype) (seed : Typed c u) (values : Audited (Typed c u)) : Entry c :=
  ⟨u,values,by
    rw [←seed.property.2]
    exact ConstructiveConstTreeTarget.output_in_table c hp seed.val seed.property.1⟩

abbrev Matched (c : context) (target : valtype) :=
  {tree : Tree // Good c tree ∧ ∀ n,SpecTecExecution.Eval SpecTec.Body
    (.call ⟨Unit,Call.Match_resulttype c [tree.output] [target]⟩)
    n (.success (.of ())) n}

def matched (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (e : Entry c) (hm : CandidateValMatch.candidateValMatch c e.type target=true) :
    Audited (Matched c target) :=
  e.values.map fun tree => ⟨tree.val,⟨tree.property.1,by
    intro n
    apply (MatchResulttypeDecision.match_pairs_iff_resulttype c _ _ n hr
      (by intro t h; have he : t=tree.val.output := by simpa using h
          subst t; simpa only [tree.property.2] using e.inTable)
      (by intro t h; have he : t=target := by simpa using h
          subst t; exact ht)).1
    simp [MatchResulttypeDecision.matchPairs,tree.property.2,hm]⟩⟩

/-- Type-directed branch selection occurs before a generator is sampled.
Only finite, already-proven output metadata is compared. -/
def eligible (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) :
    List (Entry c) → List (Audited (Matched c target))
  | [] => []
  | e::es => if hm : CandidateValMatch.candidateValMatch c e.type target=true
    then matched c hr target ht e hm :: eligible c hr target ht es
    else eligible c hr target ht es

def operand (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (table : List (Entry c)) : Option (Audited (Matched c target)) :=
  match eligible c hr target ht table with
  | [] => none
  | h::t => some (h.merge t)

def operandsCons (c : context) (t : valtype) (ts : List valtype)
    (head : Matched c t) (tail : Operands c ts) : Operands c (t::ts) :=
  ⟨head.val::tail.trees,by
    intro tree h; rcases List.mem_cons.mp h with rfl|h
    · exact head.property.1
    · exact tail.good tree h,by
    intro n
    have hh := (MatchResulttypeValidation.match_resulttype_success_iff c [head.val.output] [t] n n).1 (head.property.2 n)
    have ht := (MatchResulttypeValidation.match_resulttype_success_iff c (outputs tail.trees) ts n n).1 (tail.matching n)
    apply (MatchResulttypeValidation.match_resulttype_success_iff c _ _ n n).2
    refine ⟨by simpa [outputs] using congrArg Nat.succ ht.1,?_⟩
    obtain ⟨middle,hmatch,hrest⟩ := (MatchResulttypeValidation.match_iter_cons_success_iff c head.val.output t [] [] n n).1 hh.2
    have hcounter : middle=n := by
      exact (properties.wasm_module_ok.Execution.eval_deterministic
        (MatchResulttypeValidation.match_iter_nil_total c middle)
        hrest).2
    subst middle
    exact (MatchResulttypeValidation.match_iter_cons_success_iff c head.val.output t _ _ n n).2 ⟨n,hmatch,ht.2⟩⟩

def operands (c : context) (hr : CandidateTypeReady.Ready c)
    (table : List (Entry c)) : (need : List valtype) →
    (∀ t∈need,CandidateValMatch.InTableVal c t) → Option (Audited (Operands c need))
  | [],_ => some (Audited.pure (emptyOperands c))
  | t::ts,ht =>
    match operand c hr t (ht t (by simp)) table,
      operands c hr table ts (fun u hu => ht u (by simp [hu])) with
    | some h,some rest => some (h.bind fun a => rest.map (operandsCons c t ts a))
    | _,_ => none

#print axioms operandsCons
end properties.wasm_module_ok.ConstructiveConstTableCore
