import properties.wasm_module_ok.CandidateTypesDecision
import properties.wasm_module_ok.CandidateRectypeSearchExact

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesChoices

/-- At a fixed index, choose each passing group before constructing a tail in
its computed context. The index bounds both the head enumeration and depth. -/
def choices (c : SpecTec.context) : Nat → List (List SpecTec.type)
  | 0 => [[]]
  | n + 1 =>
      [] :: (CandidateRectypeSearchExact.candidates c (n + 1)).flatMap
        (fun rect =>
          match rect with
          | .RecT sts =>
              match CandidateRectypeTable.candidateContext c sts with
              | none => []
              | some next => (choices next n).map (fun ts => rect :: ts))

theorem choices_sound
    (c : SpecTec.context) (n : Nat) (ts : List SpecTec.type)
    (h : ts ∈ choices c n) :
    ∃ result, CandidateTypesDecision.typesResult c ts = some result := by
  induction n generalizing c ts with
  | zero =>
      have hnil : ts = [] := by simpa [choices] using h
      subst ts
      exact ⟨c, rfl⟩
  | succ n ih =>
      rcases List.mem_cons.mp h with hnil | htail
      · subst ts
        exact ⟨c, rfl⟩
      · obtain ⟨rect, hrect, hmap⟩ := List.mem_flatMap.mp htail
        cases rect with
        | RecT sts =>
            cases hcontext : CandidateRectypeTable.candidateContext c sts with
            | none => simp [hcontext] at hmap
            | some next =>
                obtain ⟨tail, htailmem, heq⟩ :=
                  List.mem_map.mp (by simpa [hcontext] using hmap)
                subst ts
                obtain ⟨result, hresult⟩ := ih next tail htailmem
                have hpass :
                    CandidateRectypeDecision.rectypePasses c sts = true :=
                  (List.mem_filter.mp hrect).2
                exact ⟨result, by
                  simp [CandidateTypesDecision.typesResult,
                    hpass, hcontext, hresult]⟩

theorem choices_mono_one
    (c : SpecTec.context) (n : Nat) (ts : List SpecTec.type)
    (h : ts ∈ choices c n) :
    ts ∈ choices c (n + 1) := by
  induction n generalizing c ts with
  | zero =>
      have hnil : ts = [] := by simpa [choices] using h
      subst ts
      exact List.mem_cons_self
  | succ n ih =>
      rcases List.mem_cons.mp h with hnil | htail
      · subst ts
        exact List.mem_cons_self
      · obtain ⟨rect, hrect, hmap⟩ := List.mem_flatMap.mp htail
        cases rect with
        | RecT sts =>
            cases hcontext : CandidateRectypeTable.candidateContext c sts with
            | none => simp [hcontext] at hmap
            | some next =>
                obtain ⟨tail, htailmem, heq⟩ :=
                  List.mem_map.mp (by simpa [hcontext] using hmap)
                subst ts
                apply List.mem_cons_of_mem
                apply List.mem_flatMap.mpr
                refine ⟨.RecT sts, ?_, ?_⟩
                · simpa [Nat.add_assoc] using
                    CandidateRectypeSearchExact.candidates_mono
                      c (n + 1) 1 (.RecT sts) hrect
                · simp only [hcontext]
                  exact List.mem_map.mpr
                    ⟨tail, ih next tail htailmem, rfl⟩

theorem choices_mono
    (c : SpecTec.context) (n k : Nat) (ts : List SpecTec.type)
    (h : ts ∈ choices c n) :
    ts ∈ choices c (n + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      simpa only [Nat.add_succ] using
        choices_mono_one c (n + k) ts ih

theorem choices_complete
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (hresult : CandidateTypesDecision.typesResult c ts = some result) :
    ∃ n, ts ∈ choices c n := by
  induction ts generalizing c result with
  | nil => exact ⟨0, by simp [choices]⟩
  | cons t ts ih =>
      cases t with
      | RecT sts =>
          by_cases hpass : CandidateRectypeDecision.rectypePasses c sts = true
          · cases hcontext : CandidateRectypeTable.candidateContext c sts with
            | none =>
                simp [CandidateTypesDecision.typesResult,
                  hpass, hcontext] at hresult
            | some next =>
                have htail :
                    CandidateTypesDecision.typesResult next ts =
                      some result := by
                  simpa [CandidateTypesDecision.typesResult,
                    hpass, hcontext] using hresult
                obtain ⟨headIndex, hdecode⟩ :=
                  Enumeration.decodeCandidates_complete
                    (SpecTec.rectype.RecT sts)
                have hhead :
                    SpecTec.rectype.RecT sts ∈
                      CandidateRectypeSearchExact.candidates c headIndex :=
                  (List.mem_filter).2 ⟨hdecode, hpass⟩
                obtain ⟨tailIndex, htailmem⟩ :=
                  ih next result htail
                let fuel := headIndex + tailIndex + 1
                have hhead' :
                    SpecTec.rectype.RecT sts ∈
                      CandidateRectypeSearchExact.candidates c (fuel + 1) := by
                  have hm :=
                    CandidateRectypeSearchExact.candidates_mono
                      c headIndex (tailIndex + 2) (.RecT sts) hhead
                  have hidx : headIndex + (tailIndex + 2) =
                      fuel + 1 := by dsimp [fuel]; omega
                  rw [hidx] at hm
                  exact hm
                have htail' : ts ∈ choices next fuel := by
                  have hm := choices_mono next tailIndex
                    (headIndex + 1) ts htailmem
                  have hidx : tailIndex + (headIndex + 1) =
                      fuel := by dsimp [fuel]; omega
                  rw [hidx] at hm
                  exact hm
                refine ⟨fuel + 1, ?_⟩
                apply List.mem_cons_of_mem
                apply List.mem_flatMap.mpr
                refine ⟨.RecT sts, hhead', ?_⟩
                simp only [hcontext]
                exact List.mem_map.mpr ⟨ts, htail', rfl⟩
          · simp [CandidateTypesDecision.typesResult, hpass] at hresult

end properties.wasm_module_ok.CandidateTypesChoices
