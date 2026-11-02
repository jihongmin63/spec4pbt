import properties.wasm_module_ok.ConstructiveConstGeneration
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTargetPlan
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableExpand properties.wasm_module_ok.ConstructiveConstTableCoverage
open properties.wasm_module_ok.ConstructiveConstGeneration

theorem eligible_nonempty (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) (table : List (Entry c)) :
    eligible c hr target ht table≠[] ↔
      ∃e∈table,CandidateValMatch.candidateValMatch c e.type target=true := by
  induction table with
  | nil => simp [eligible]
  | cons e es ih =>
    by_cases hm : CandidateValMatch.candidateValMatch c e.type target=true
    · simp [eligible,hm]
    · simp [eligible,hm,ih]

theorem operand_found (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) (table : List (Entry c)) :
    (∃g,operand c hr target ht table=some g) ↔
      ∃e∈table,CandidateValMatch.candidateValMatch c e.type target=true := by
  rw [←eligible_nonempty c hr target ht table]
  cases he : eligible c hr target ht table <;> simp [operand,he]

theorem found_mono (c : context) (hr : CandidateTypeReady.Ready c)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (a b : List (Entry c)) (hsub : a⊆b)
    (h : ∃g,operand c hr target ht a=some g) :
    ∃g,operand c hr target ht b=some g := by
  obtain ⟨e,he,hm⟩ := (operand_found c hr target ht a).1 h
  exact (operand_found c hr target ht b).2 ⟨e,hsub he,hm⟩

/-- A productive target is represented by a finite expansion round plus an
ERASED proof that the corresponding metadata offers an operand generator.
No completed AST or validity test is stored in the plan. -/
structure Plan (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) where
  start : Nat
  found : ∃g,operand c hr target ht (rounds c hr hp hn start)=some g

def planAt (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) (n : Nat) :
    Option (Plan c hr hp hn target ht) :=
  match h : operand c hr target ht (rounds c hr hp hn n) with
  | none => none
  | some g => some ⟨n,⟨g,h⟩⟩

def advance (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (n : Nat) : Audited (Matched c target) :=
  match he : operand c hr target ht (rounds c hr hp hn (plan.start+n)) with
  | some g => g
  | none => False.elim (by
      obtain ⟨g,hg⟩ := found_mono c hr target ht _ _
        (rounds_monotone c hr hp hn plan.start n) plan.found
      rw [he] at hg
      cases hg)

def matchedTrees (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) : Gen (Matched c target) :=
  Gen.arbNat >>= fun n => (advance c hr hp hn target ht plan n).generator

def constants (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) : Gen (List instr) :=
  (fun tree => tree.val.code) <$> matchedTrees c hr hp hn target ht plan

theorem matchedTrees_audit (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) : Structural (matchedTrees c hr hp hn target ht plan) :=
  ⟨arbNat_audit,fun n => (advance c hr hp hn target ht plan n).audit⟩

theorem constants_audit (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) : Structural (constants c hr hp hn target ht plan) :=
  (map_audit _ _).2 (matchedTrees_audit c hr hp hn target ht plan)

theorem advance_covers (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (n : Nat) (tree : Matched c target)
    (hc : Covers (rounds c hr hp hn (plan.start+n)) tree.val) :
    Gen.support (advance c hr hp hn target ht plan n).generator tree := by
  obtain ⟨g,hg,hs⟩ := operand_cover c hr target ht _ tree hc
  unfold advance
  split
  · rename_i g' he
    rw [hg] at he
    cases he
    exact hs
  · rename_i he
    rw [hg] at he
    cases he

#print axioms constants_audit
end properties.wasm_module_ok.ConstructiveConstTargetPlan
