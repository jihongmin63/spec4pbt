import properties.wasm_module_ok.PopGeneralValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.PopLength

theorem pop_noellipses_success_requires_length
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) fin) :
    need.length ≤ available.length := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, need) (.NoEllipses, available)))
      start (.success (.of result)) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (properties.wasm_module_ok.Execution.tryClauses_success_iff
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
                  simp at htail
                  cases htail with
                  | bind_success _ htail =>
                    simp at htail
                    cases htail with
                    | bind_success _ htail =>
                      cases htail with
                      | bind_success hmatch _ =>
                        have hlen :=
                          (MatchResulttypeValidation.match_resulttype_success_iff
                            c _ need _ _).1 hmatch |>.1
                        simp [List.length_take, List.length_drop] at hlen
                        omega
          | next _ hnone => cases hnone

end properties.wasm_module_ok.PopLength
