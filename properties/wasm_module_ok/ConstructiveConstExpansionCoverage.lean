import properties.wasm_module_ok.ConstructiveConstSeedCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstExpansionCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage

theorem fromOperands_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (table : List (Entry c)) (need : List valtype)
    (hnt : ∀t∈need,CandidateValMatch.InTableVal c t)
    (u : valtype) (hu : CandidateValMatch.InTableVal c u)
    (build : Operands c need → Typed c u) (args : Operands c need)
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (fromOperands c hr table need hnt u hu build) (build args).val := by
  obtain ⟨g,hg,hs⟩ := operands_cover c hr table need hnt args hc
  unfold fromOperands
  rw [hg]
  exact ⟨⟨u,g.map build,hu⟩,by simp,build args,⟨args,hs,rfl⟩,rfl⟩

theorem struct_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (index : StructIndex c) (args : Operands c (StructExplicitFieldsDecision.structFieldInputs index.fields))
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (structEntries c hr hn table) (structExplicit c index args).val := by
  unfold structEntries
  apply covers_flatMap index (struct_index_mem c index)
  exact fromOperands_cover c hr table _ _ _ _ _ args hc

theorem array_explicit_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (index : ArrayIndex c)
    (args : Operands c [UnpackedFieldDecision.unpackedFieldResult index.field,.NumT .I32T])
    (hc : ∀t∈args.trees,Covers table t) :
    Covers (arrayEntries c hr hn table) (arrayExplicit c index args).val := by
  unfold arrayEntries
  apply covers_flatMap index (array_index_mem c index)
  apply covers_mono (fun e he => List.mem_append_left _ (List.mem_append_left _ he))
  exact fromOperands_cover c hr table _ _ _ _ _ args hc

theorem array_implicit_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (hn : CandidateNestedReady.nestedTableReady c=true) (table : List (Entry c))
    (index : ArrayIndex c)
    (hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult index.field)=true)
    (args : Operands c [.NumT .I32T]) (hc : ∀t∈args.trees,Covers table t) :
    Covers (arrayEntries c hr hn table) (arrayImplicit c index hd args).val := by
  unfold arrayEntries
  apply covers_flatMap index (array_index_mem c index)
  apply covers_mono (fun e he => List.mem_append_left _ (List.mem_append_right _ he))
  simp only [dif_pos hd]
  exact fromOperands_cover c hr table _ _ _ _ _ args hc

theorem repeat_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (table : List (Entry c)) (u : valtype) (hu : CandidateValMatch.InTableVal c u)
    (g : Audited (Matched c u)) (hg : operand c hr u hu table=some g)
    (n : Nat) (out : Operands c (List.replicate n u))
    (hc : ∀t∈out.trees,Covers table t) :
    Gen.support (repeatOperands c u g n).generator out := by
  have hm := (MatchResulttypeDecision.match_pairs_iff_resulttype c (outputs out.trees) (List.replicate n u) 0 hr
    (by intro t ht; obtain ⟨tree,hm,rfl⟩ := List.mem_map.mp ht
        exact covers_inTable (hc tree hm))
    (by intro t ht; have he : t=u := (List.mem_replicate.mp ht).2
        subst t; exact hu)).2 (out.matching 0)
  induction n with
  | zero =>
    cases trees : out.trees with
    | nil => exact operands_ext trees
    | cons a as => simp [outputs,trees,MatchResulttypeDecision.matchPairs] at hm
  | succ n ih =>
    cases trees : out.trees with
    | nil => simp [outputs,trees,MatchResulttypeDecision.matchPairs,List.replicate_succ] at hm
    | cons a as =>
      have hm' : CandidateValMatch.candidateValMatch c a.output u=true ∧
          MatchResulttypeDecision.matchPairs c (outputs as) (List.replicate n u)=true := by
        simpa [outputs,trees,MatchResulttypeDecision.matchPairs,List.replicate_succ] using hm
      have hta : CandidateValMatch.InTableVal c a.output := covers_inTable (hc a (by simp [trees]))
      let head : Matched c u := ⟨a,out.good a (by simp [trees]),by
        intro k
        exact (MatchResulttypeDecision.match_pairs_iff_resulttype c [a.output] [u] k hr
          (by intro t h; have he : t=a.output := by simpa using h
              subst t; exact hta)
          (by intro t h; have he : t=u := by simpa using h
              subst t; exact hu)).1 (by simp [MatchResulttypeDecision.matchPairs,hm'.1])⟩
      let rest : Operands c (List.replicate n u) := ⟨as,(fun t ht => out.good t (by simp [trees,ht])),by
        intro k
        exact (MatchResulttypeDecision.match_pairs_iff_resulttype c (outputs as) (List.replicate n u) k hr
          (by intro t h; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
              exact covers_inTable (hc v (by simp [trees,hv])))
          (by intro t ht; have he : t=u := (List.mem_replicate.mp ht).2
              subst t; exact hu)).1 hm'.2⟩
      obtain ⟨gh,hgh,hsh⟩ := operand_cover c hr u hu table head (hc a (by simp [trees]))
      rw [hg] at hgh
      cases hgh
      have hst := ih rest (fun t h => hc t (by simp [rest,trees] at h ⊢; exact Or.inr h)) hm'.2
      exact ⟨head,hsh,rest,hst,operands_ext trees⟩

#print axioms struct_cover
#print axioms repeat_cover
end properties.wasm_module_ok.ConstructiveConstExpansionCoverage
