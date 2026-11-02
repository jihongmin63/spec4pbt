import properties.wasm_module_ok.ConstructiveConstTreeComplete
import properties.wasm_module_ok.ConstructiveConstTargetPlan
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstTargetExact
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableExpand properties.wasm_module_ok.ConstructiveConstTableCoverage
open properties.wasm_module_ok.ConstructiveConstGeneration properties.wasm_module_ok.ConstructiveConstTreeComplete properties.wasm_module_ok.ConstructiveConstTargetPlan

theorem matchedTrees_complete (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (tree : Matched c target) :
    Gen.support (matchedTrees c hr hp hn target ht plan) tree := by
  obtain ⟨n,hcov⟩ := good_covered c hr hp hn tree.val tree.property.1
  have hc := covers_mono (rounds_monotone c hr hp hn n plan.start) hcov
  exact ⟨n,by simp,advance_covers c hr hp hn target ht plan n tree
    (by simpa only [Nat.add_comm n plan.start] using hc)⟩

theorem constants_sound (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (xs : List instr)
    (hs : Gen.support (constants c hr hp hn target ht plan) xs) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) n (.success (.of ())) n := by
  obtain ⟨tree,_,rfl⟩ := hs
  exact tree_const_ok c tree.val tree.property.1 target n (tree.property.2 n)

theorem constants_complete (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) start (.success (.of ())) finish) :
    Gen.support (constants c hr hp hn target ht plan) xs := by
  obtain ⟨tree,hgood,hcode,hmatch⟩ := ConstructiveConstTreeTarget.const_tree_target c hr hp hn target ht xs start finish h
  exact ⟨⟨tree,hgood,hmatch⟩,matchedTrees_complete c hr hp hn target ht plan _,hcode.symm⟩

theorem constants_exact (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (plan : Plan c hr hp hn target ht) (xs : List instr) (n : Nat) :
    Gen.support (constants c hr hp hn target ht plan) xs ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) n (.success (.of ())) n :=
  ⟨fun h => constants_sound c hr hp hn target ht plan xs h n,
   constants_complete c hr hp hn target ht plan xs n n⟩

theorem planAt_found (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target) (n : Nat)
    (h : ∃g,operand c hr target ht (rounds c hr hp hn n)=some g) :
    ∃plan,planAt c hr hp hn target ht n=some plan ∧ plan.start=n := by
  unfold planAt
  split
  · rename_i he
    obtain ⟨g,hg⟩ := h
    rw [he] at hg
    cases hg
  · exact ⟨_,rfl,rfl⟩

/-- Every original successful constant supplies a finite productive metadata
round. This is backward coverage, not a validity assumption on generated code. -/
theorem original_has_plan (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (target : valtype) (ht : CandidateValMatch.InTableVal c target)
    (xs : List instr) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Const_ok c target xs⟩) start (.success (.of ())) finish) :
    ∃n plan,planAt c hr hp hn target ht n=some plan := by
  obtain ⟨tree,hgood,hcode,hmatch⟩ := ConstructiveConstTreeTarget.const_tree_target c hr hp hn target ht xs start finish h
  obtain ⟨n,hcov⟩ := good_covered c hr hp hn tree hgood
  obtain ⟨g,hg,_⟩ := operand_cover c hr target ht _ ⟨tree,hgood,hmatch⟩ hcov
  obtain ⟨plan,hplan,_⟩ := planAt_found c hr hp hn target ht n ⟨g,hg⟩
  exact ⟨n,plan,hplan⟩

#print axioms constants_exact
#print axioms original_has_plan
end properties.wasm_module_ok.ConstructiveConstTargetExact
