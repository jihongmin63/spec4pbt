import properties.wasm_module_ok.ConstructiveConstExpansionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstFixedCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstExpansionCoverage

theorem array_fixed_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (index : ArrayIndex c) (count : Nat) (hcount : count≠0)
    (args : Operands c (MakeValidation.makeResult (UnpackedFieldDecision.unpackedFieldResult index.field) count))
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (arrayEntries c hr hn table) (arrayFixed c index count args).val := by
  let u := UnpackedFieldDecision.unpackedFieldResult index.field
  have hu : CandidateValMatch.InTableVal c u :=
    ConstExtendedCandidateReady.array_field_in_table c hn index.index index.field
      (by simp [ArrayTypeDecision.arrayTypeResult,index.lookup,index.expansion])
  let args' : Operands c (List.replicate count u) := ⟨args.trees,args.good,by
    simpa only [make_replicate] using args.matching⟩
  have hm := (MatchResulttypeDecision.match_pairs_iff_resulttype c (outputs args'.trees) (List.replicate count u) 0 hr
    (by intro t ht; obtain ⟨tree,hm,rfl⟩ := List.mem_map.mp ht
        exact covers_inTable (hc tree hm))
    (by intro t ht; have he : t=u := (List.mem_replicate.mp ht).2
        subst t; exact hu)).2 (args'.matching 0)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcount
  cases trees : args'.trees with
  | nil => simp [outputs,trees,MatchResulttypeDecision.matchPairs,List.replicate_succ] at hm
  | cons a as =>
    have hm' : CandidateValMatch.candidateValMatch c a.output u=true := by
      exact (Bool.and_eq_true_iff.mp (by simpa [outputs,trees,MatchResulttypeDecision.matchPairs,List.replicate_succ] using hm)).1
    let head : Matched c u := ⟨a,args'.good a (by simp [trees]),by
      intro k
      exact (MatchResulttypeDecision.match_pairs_iff_resulttype c [a.output] [u] k hr
        (by intro t h; have he : t=a.output := by simpa using h
            subst t; exact covers_inTable (hc a (by change a∈args'.trees; simp [trees])))
        (by intro t h; have he : t=u := by simpa using h
            subst t; exact hu)).1 (by simp [MatchResulttypeDecision.matchPairs,hm'])⟩
    obtain ⟨g,hg,hs⟩ := operand_cover c hr u hu table head
      (hc a (by change a∈args'.trees; simp [trees]))
    have hall := repeat_cover c hr table u hu g hg (n+1) args' hc
    unfold arrayEntries
    apply covers_flatMap index (array_index_mem c index)
    apply covers_mono (fun e he => List.mem_append_right _ he)
    dsimp only [u] at hg ⊢
    rw [hg]
    refine ⟨fixedArrays c index g,by simp,arrayFixed c index (n+1) args,?_,rfl⟩
    dsimp only [fixedArrays,Audited.bind,Audited.map]
    simp only [Gen.Support.support_bind,Gen.Support.support_map]
    exact ⟨n+1,by simp,args',hall,Subtype.ext rfl⟩

#print axioms array_fixed_cover
end properties.wasm_module_ok.ConstructiveConstFixedCoverage
