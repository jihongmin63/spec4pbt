import properties.wasm_module_ok.CandidateValMembership

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateUniverseReady

/-- The extra candidates copied from function and global context fields must
come from types that the ready matcher can actually inspect. -/
structure Provenance (c : SpecTec.context) : Prop where
  funcs : ∀ dt, dt ∈ c.FUNCS → dt ∈ c.TYPES
  globals : ∀ gt, gt ∈ c.GLOBALS →
    CandidateValMatch.InTableVal c
      (match gt with | .GlobalT _ t => t)

theorem candidate_universe_in_table
    (c : SpecTec.context) (t : SpecTec.valtype)
    (hprov : Provenance c)
    (h : t ∈ FiniteValidTypes.candidateUniverse c) :
    CandidateValMatch.InTableVal c t := by
  simp only [FiniteValidTypes.candidateUniverse, List.mem_toFinset,
    FiniteValidTypes.candidateTypes, List.mem_append] at h
  rcases h with (hvalid | hinternal) | hglobal
  · exact CandidateValMembership.valid_candidate_in_table c t hvalid
  · simp only [FiniteValidTypes.internalRefCandidates,
      List.mem_flatMap] at hinternal
    obtain ⟨dt, hdt, hshape⟩ := hinternal
    have hdtTypes : dt ∈ c.TYPES := by
      rcases List.mem_append.mp hdt with htype | hfunc
      · exact htype
      · exact hprov.funcs dt hfunc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hshape
    rcases hshape with hfirst | hsecond
    · subst t
      exact CandidateValMembership.table_definition_in_table
        c dt hdtTypes .NoNull
    · subst t
      exact CandidateValMembership.table_definition_in_table
        c dt hdtTypes .Null
  · obtain ⟨gt, hgt, rfl⟩ := List.mem_map.mp hglobal
    exact hprov.globals gt hgt

theorem candidate_universe_match_iff
    (c : SpecTec.context) (u t : SpecTec.valtype)
    (b : Bool) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : Provenance c)
    (hu : u ∈ FiniteValidTypes.candidateUniverse c)
    (ht : t ∈ FiniteValidTypes.candidateUniverse c) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» c.TYPES u t⟩)
      start (.success (.of b)) finish ↔
    b = CandidateValMatch.candidateValMatch c u t ∧ finish = start := by
  exact CandidateValMatch.candidate_val_match_iff c u t b start finish
    hready (candidate_universe_in_table c u hprov hu)
    (candidate_universe_in_table c t hprov ht)

end properties.wasm_module_ok.CandidateUniverseReady
