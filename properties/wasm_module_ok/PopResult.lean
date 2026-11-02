import properties.wasm_module_ok.PopLength

set_option autoImplicit false

namespace properties.wasm_module_ok.PopResult

theorem pop_noellipses_success_result
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) fin) :
    result = (.NoEllipses,
      available.take (available.length - need.length)) := by
  have hlen := PopLength.pop_noellipses_success_requires_length
    c need available result start fin h
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, need) (.NoEllipses, available)))
      start (.success (.of result)) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.tryClauses_success_iff
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, need) (.NoEllipses, available))
        start (.of result) fin).1 hbody
    unfold SpecTec.«$pop_clauses» at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«$pop:clause:0» at h0
      cases h0 with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
    | next _ hselected =>
      cases hselected with
      | here h1 =>
        unfold SpecTec.«$pop:clause:1» at h1
        cases h1 with
        | bind_success _ htail =>
          cases htail with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
      | next _ hselected =>
        cases hselected with
        | here h2 =>
          unfold SpecTec.«$pop:clause:2» at h2
          cases h2 with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
        | next _ hselected =>
          cases hselected with
          | here h3 =>
            unfold SpecTec.«$pop:clause:3» at h3
            cases h3 with
            | bind_success _ htail =>
              cases htail with
              | bind_success _ htail =>
                cases htail with
                | bind_success hmin htail =>
                  have hminval := (MinValidation.min_success_iff
                    need.length available.length _ _ _).1 hmin
                  rcases hminval with ⟨rfl, rfl⟩
                  have hdiff :
                      Int.ofNat available.length - Int.ofNat
                        (min need.length available.length) =
                        Int.ofNat (available.length -
                          min need.length available.length) :=
                    (Int.ofNat_sub (Nat.min_le_right _ _)).symm
                  simp only [hdiff, Int.toNat?] at htail
                  simp [Nat.min_eq_left hlen] at htail
                  cases htail with
                  | bind_success _ htail =>
                    simp at htail
                    cases htail with
                    | bind_success _ htail =>
                      cases htail with
                      | bind_success _ htail =>
                        cases htail with
                        | bind_success _ hpure =>
                          cases hpure
                          rfl
          | next _ hnone => cases hnone

theorem pop_noellipses_result_entries_from_input
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) fin)
    (t : SpecTec.valtype) (ht : t ∈ result.2) :
    t ∈ available := by
  have hr := pop_noellipses_success_result c need available result start fin h
  rw [hr] at ht
  exact List.mem_of_mem_take ht

end properties.wasm_module_ok.PopResult
