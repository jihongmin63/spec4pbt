import properties.wasm_module_ok.PopGeneralValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.PopNumericPair

theorem match_nil_pair_impossible
    (c : SpecTec.context) (nt : SpecTec.numtype)
    (start fin : Nat) :
    ¬ SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c
        ([] : List SpecTec.valtype) [.NumT nt, .NumT nt]⟩)
      start (.success (.of ())) fin := by
  intro h
  have hlen := (MatchResulttypeValidation.match_resulttype_success_iff
    c [] [.NumT nt, .NumT nt] start fin).1 h |>.1
  simp at hlen

theorem pop_numeric_pair_from_empty_impossible
    (c : SpecTec.context) (nt : SpecTec.numtype)
    (result : SpecTec.inferresulttype) (start fin : Nat) :
    ¬ SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [.NumT nt, .NumT nt]) (.NoEllipses, [])⟩)
      start (.success (.of result)) fin := by
  intro h
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, [.NumT nt, .NumT nt]) (.NoEllipses, [])) ())
      start (.success (.of result)) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, [.NumT nt, .NumT nt]) (.NoEllipses, [])) ()
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
            simp only [List.length_nil, List.length_cons] at h3
            cases h3 with
            | bind_success _ htail =>
              cases htail with
              | bind_success _ htail =>
                cases htail with
                | bind_success hmin htail =>
                  have hminval := (MinValidation.min_success_iff 2 0 _ _ _).1 hmin
                  rcases hminval with ⟨rfl, rfl⟩
                  simp at htail
                  cases htail with
                  | bind_success _ htail =>
                    simp at htail
                    cases htail with
                    | bind_success _ htail =>
                      cases htail with
                      | bind_success hmatch _ =>
                        exact match_nil_pair_impossible c nt _ _ hmatch
          | next _ hnone => cases hnone

end properties.wasm_module_ok.PopNumericPair
